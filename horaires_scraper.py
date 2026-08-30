# -*- coding: utf-8 -*-
import argparse
import concurrent.futures
import os
import random
import re
import subprocess
import threading
import time
import pandas as pd
import requests
from bs4 import BeautifulSoup

try:
	from ddgs import DDGS
except ImportError:
	from duckduckgo_search import DDGS

HEADERS = {
	"User-Agent": "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/126.0.0.0 Safari/537.36",
	# On ne demande que du HTML/XML : ça évite au serveur de nous pousser des variantes lourdes
	# et ça sert de signal (certains CDN adaptent la réponse selon l'Accept).
	"Accept": "text/html,application/xhtml+xml,application/xml;q=0.9,*/*;q=0.1",
	"Accept-Language": "fr-FR,fr;q=0.9",
	# On accepte la compression (réduit fortement le volume transféré pour du texte)
	"Accept-Encoding": "gzip, deflate, br",
}

# Types de contenu qu'on refuse de télécharger (images, vidéos, sons, fichiers lourds...)
BLOCKED_CONTENT_TYPES = [
	"image/", "video/", "audio/", "font/",
	"application/pdf", "application/zip", "application/octet-stream",
	"application/vnd.", "application/x-", "application/msword",
]

# On ne garde que ce qui ressemble à du HTML
ALLOWED_CONTENT_TYPES = ["text/html", "application/xhtml+xml"]

# Taille max de contenu qu'on lit par page (les horaires se trouvent quasi toujours
# dans les premiers Ko du HTML : pas besoin de tout télécharger)
MAX_HTML_BYTES = 400_000  # ~400 Ko

# Balises qu'on supprime avant extraction du texte : elles ne servent jamais aux horaires
# et peuvent référencer des ressources lourdes (mais surtout, on ne veut pas leur texte/alt parasite)
STRIP_TAGS = ["script", "style", "img", "picture", "source", "video", "audio",
              "iframe", "svg", "noscript", "canvas", "embed", "object"]

BLOCKED_MARKERS = [
	"access denied", "accès refusé", "acces refuse", "captcha",
	"unusual traffic", "please verify you are a human", "verify you are a human",
	"cloudflare", "attention required", "403 forbidden", "just a moment",
	"vérification en cours", "verification en cours", "pardon our interruption", "are you a robot"
]

# Colonnes ajoutées au fichier de sortie
STATUS_COLUMNS = ["Horaires", "Source Horaires", "URL Source Horaires", "Statut Horaires", "Commentaire Horaires"]

SESSION = requests.Session()
SESSION.headers.update(HEADERS)
WRITE_LOCK = threading.Lock()

COMMIT_EVERY_N_SAVES = 5
_save_counter = {"n": 0}
_commit_lock = threading.Lock()

# ---------------------------------------------------------------------------
# Lecture / normalisation (identique au script diplômes)
# ---------------------------------------------------------------------------

def read_table(path):
	trials = [("utf-8", ","), ("utf-8", ";"), ("utf-8", "\t"), ("utf-8-sig", ","), ("utf-8-sig", ";"),
	          ("utf-8-sig", "\t"), ("cp1252", ","), ("cp1252", ";"), ("cp1252", "\t")]
	for enc, sep in trials:
		try:
			df = pd.read_csv(path, encoding=enc, sep=sep)
			if len(df.columns) >= 2:
				return df
		except Exception:
			pass
	raise ValueError(f"Impossible de lire le fichier : {path}")

def normalize_columns(df):
	rename_map = {col: str(col).strip().replace("Pr?nom", "Prénom").replace("Sp?cialit? M?dicale", "Spécialité Médicale") for col in df.columns}
	return df.rename(columns=rename_map)

def ensure_status_columns(df):
	for col in STATUS_COLUMNS:
		df[col] = df[col].fillna("") if col in df.columns else ""
	return df

def load_dataframe(input_file, output_file):
	if os.path.exists(output_file):
		df = ensure_status_columns(normalize_columns(read_table(output_file)))
		if os.path.exists(input_file):
			df_input = normalize_columns(read_table(input_file))
			key_cols = [c for c in ["Nom", "Prénom"] if c in df.columns and c in df_input.columns]
			if key_cols:
				existing_keys = set(map(tuple, df[key_cols].astype(str).values))
				df_input["_key"] = list(map(tuple, df_input[key_cols].astype(str).values))
				new_rows = df_input[~df_input["_key"].isin(existing_keys)].drop(columns="_key")
				if len(new_rows) > 0:
					df = pd.concat([df, ensure_status_columns(new_rows)], ignore_index=True)
		return df
	df = ensure_status_columns(normalize_columns(read_table(input_file)))
	return df

def git_commit_and_push(file_path, message):
	if os.environ.get("GITHUB_ACTIONS") != "true":
		return
	with _commit_lock:
		try:
			subprocess.run(["git", "add", file_path], check=True)
			if subprocess.run(["git", "diff", "--cached", "--quiet"]).returncode == 0:
				return
			subprocess.run(["git", "config", "--global", "user.name", "github-actions[bot]"], check=True)
			subprocess.run(["git", "config", "--global", "user.email", "github-actions[bot]@users.noreply.github.com"], check=True)
			subprocess.run(["git", "commit", "-m", message], check=True)
			subprocess.run(["git", "pull", "--rebase", "--autostash"], check=True)
			subprocess.run(["git", "push"], check=True)
		except Exception as e:
			print(f"[GIT] Erreur commit/push : {e}")

def safe_get(row, *names):
	for name in names:
		if name in row and pd.notna(row[name]):
			return str(row[name]).strip()
	return ""

def full_name(row):
	return f"{safe_get(row, 'Prénom', 'Prenom', 'Pr?nom')} {safe_get(row, 'Nom')}".strip()

# ---------------------------------------------------------------------------
# Extraction des horaires
# ---------------------------------------------------------------------------

DAYS = ["Lundi", "Mardi", "Mercredi", "Jeudi", "Vendredi", "Samedi", "Dimanche"]
DAY_PATTERN = "|".join(DAYS)
TIME = r"\d{1,2}\s?[h:]\s?\d{0,2}"
RANGE = rf"{TIME}\s*[-–à]\s*{TIME}"

BLOCK_RE = re.compile(rf"({DAY_PATTERN})\s*:?\s*((?:{RANGE}\s*(?:/|et|,)?\s*)+)", re.IGNORECASE)
CLOSED_RE = re.compile(rf"({DAY_PATTERN})\s*:?\s*(ferm[ée])", re.IGNORECASE)
GENERIC_HOURS_RE = re.compile(rf"(?:horaires?|ouvert(?:ure)?s?)[^\.\n]{{0,40}}?({RANGE})", re.IGNORECASE)

BLACKLIST_SNIPPETS = ["cookies", "mentions légales", "politique de confidentialité", "pagesjaunes.fr"]

def extract_hours_info(text):
	"""Analyse le texte pour en extraire un bloc d'horaires d'ouverture plausible."""
	if not text:
		return None

	text_lower = text.lower()
	if any(b in text_lower for b in BLACKLIST_SNIPPETS):
		for b in BLACKLIST_SNIPPETS:
			text = re.sub(rf'.*?{re.escape(b)}.*?([\.\n]|$)', '', text, flags=re.IGNORECASE)

	matches = list(BLOCK_RE.finditer(text)) + list(CLOSED_RE.finditer(text))
	if matches:
		matches.sort(key=lambda m: m.start())
		parts, seen_days = [], set()
		for m in matches:
			day = m.group(1).capitalize()
			if day in seen_days:
				continue
			seen_days.add(day)
			snippet = re.sub(r'\s+', ' ', m.group(0).strip())
			parts.append(snippet)
		if parts:
			return " | ".join(parts)

	generic = GENERIC_HOURS_RE.search(text)
	if generic:
		start = max(0, generic.start() - 20)
		end = min(len(text), generic.end() + 10)
		return re.sub(r'\s+', ' ', text[start:end].strip())

	return None

def search_web(query, max_results=5, max_retries=3):
	for attempt in range(1, max_retries + 1):
		try:
			results = []
			with DDGS() as ddgs:
				for item in ddgs.text(query, region="fr-fr", max_results=max_results):
					results.append({"title": item.get("title", ""), "url": item.get("href", ""), "body": item.get("body", "")})
			return results
		except Exception:
			time.sleep(attempt * random.uniform(2.0, 4.0))
	return []

def fetch_html_only(url, timeout=15):
	"""
	Récupère une page en évitant de télécharger images/vidéos/fichiers lourds :
	- Vérifie le Content-Type AVANT de lire le corps (via un flux, stream=True)
	- Coupe la lecture au bout de MAX_HTML_BYTES
	- Referme la connexion proprement dans tous les cas
	Retourne le texte HTML (str) ou None si la page est refusée/illisible.
	"""
	r = None
	try:
		r = SESSION.get(url, timeout=timeout, allow_redirects=True, stream=True)

		if r.status_code != 200:
			return None

		content_type = r.headers.get("Content-Type", "").lower()

		# Type explicitement bloqué (image, vidéo, pdf, zip...) -> on ne lit rien
		if any(bad in content_type for bad in BLOCKED_CONTENT_TYPES):
			return None

		# Si le type n'est ni "autorisé" ni vide, on est prudent et on ignore
		if content_type and not any(ok in content_type for ok in ALLOWED_CONTENT_TYPES):
			return None

		# Optionnel : certains serveurs renvoient Content-Length -> on peut couper avant même de streamer
		content_length = r.headers.get("Content-Length")
		if content_length and content_length.isdigit() and int(content_length) > MAX_HTML_BYTES * 3:
			# Page anormalement énorme pour du HTML classique : probablement pas pertinent, on saute
			return None

		raw = b""
		for chunk in r.iter_content(chunk_size=8192):
			if not chunk:
				break
			raw += chunk
			if len(raw) >= MAX_HTML_BYTES:
				break  # on a assez lu, pas besoin du reste de la page

		encoding = r.encoding or "utf-8"
		return raw.decode(encoding, errors="ignore")
	except Exception:
		return None
	finally:
		if r is not None:
			r.close()

def enrich_row(index, row):
	name = full_name(row)
	if str(row.get("Statut Horaires", "")).strip() in ["Trouvé", "Non trouvé"]:
		return index, {}

	ville = safe_get(row, "Ville")
	specialite = safe_get(row, "Spécialité Médicale")

	queries = [
		f'"Dr {name}" {ville} horaires cabinet médical',
		f'"{name}" {specialite} {ville} "horaires" ouverture',
	]

	seen_urls = set()

	# Les 2 requêtes du docteur partent simultanément (1 thread par requête)
	with concurrent.futures.ThreadPoolExecutor(max_workers=2) as query_executor:
		future_to_query = {query_executor.submit(search_web, q): q for q in queries}
		for future in concurrent.futures.as_completed(future_to_query):
			try:
				results = future.result()
			except Exception:
				results = []
			for r in results:
				url = r.get("url", "")
				if any(x in url for x in ["facebook.com"]):
					continue
				horaires = extract_hours_info(r.get("body", "") + " " + r.get("title", ""))
				if horaires:
					source = url.split("/")[2] if "//" in url else url
					return index, {
						"Horaires": horaires, "Source Horaires": source, "URL Source Horaires": url,
						"Statut Horaires": "Trouvé", "Commentaire Horaires": "Trouvé via snippet"
					}
				if url:
					seen_urls.add(url)

	time.sleep(random.uniform(0.5, 1.5))

	for url in list(seen_urls)[:4]:
		# On évite de télécharger des URL qui pointent clairement vers un fichier lourd
		# avant même d'envoyer la requête (extension explicite dans le lien)
		if re.search(r"\.(jpg|jpeg|png|gif|webp|svg|mp4|mp3|avi|mov|pdf|zip|rar|docx?|pptx?)(\?|$)", url, re.IGNORECASE):
			continue

		html_text = fetch_html_only(url)
		if html_text and not any(m in html_text.lower() for m in BLOCKED_MARKERS):
			soup = BeautifulSoup(html_text, "lxml")
			for s in soup(STRIP_TAGS):
				s.decompose()
			horaires = extract_hours_info(soup.get_text())
			if horaires:
				source = url.split("/")[2] if "//" in url else url
				return index, {
					"Horaires": horaires, "Source Horaires": source, "URL Source Horaires": url,
					"Statut Horaires": "Trouvé", "Commentaire Horaires": "Trouvé sur la page"
				}
		time.sleep(random.uniform(1.0, 2.0))

	return index, {
		"Horaires": "", "Source Horaires": "", "URL Source Horaires": "",
		"Statut Horaires": "Non trouvé", "Commentaire Horaires": "Aucun horaire trouvé"
	}

def process_dataframe(df, max_workers, output_file):
	global _save_counter
	total = len(df)
	with concurrent.futures.ThreadPoolExecutor(max_workers=max_workers) as executor:
		futures = {executor.submit(enrich_row, idx, row): idx for idx, row in df.iterrows()}
		for i, future in enumerate(concurrent.futures.as_completed(futures), 1):
			idx, updates = future.result()
			if updates:
				with WRITE_LOCK:
					for col, val in updates.items():
						df.at[idx, col] = val
					df.to_csv(output_file, index=False, encoding="utf-8-sig", sep=";")
					_save_counter["n"] += 1
					if _save_counter["n"] >= COMMIT_EVERY_N_SAVES:
						_save_counter["n"] = 0
						git_commit_and_push(output_file, f"Progression horaires : {i}/{total}")
			print(f"Progression : {i}/{total}")
	df.to_csv(output_file, index=False, encoding="utf-8-sig", sep=";")
	git_commit_and_push(output_file, "Fin traitement horaires")

if __name__ == "__main__":
	parser = argparse.ArgumentParser()
	parser.add_argument("--max-concurrent", type=int, default=2)
	parser.add_argument("--input", type=str, default="medecins.csv")
	parser.add_argument("--output", type=str, default="medecins_horaires_enrichi.csv")
	args = parser.parse_args()
	df_data = load_dataframe(args.input, args.output)
	process_dataframe(df_data, args.max_concurrent, args.output)