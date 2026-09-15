# -*- coding: utf-8 -*-
"""
Trouver les e-mails d'une liste de sites web (crawling), sur le même principe
que le script Google Apps Script fourni :

  1. On visite la page d'accueil du site.
  2. On repère les liens "secondaires" utiles (contact, à propos, mentions
     légales, CGV...) et on les visite aussi (jusqu'à 3).
  3. Sur chaque page, on extrait les adresses e-mail présentes, puis on ne
     garde QUE celles dont le domaine contient un mot-clé du nom de domaine
     du site (ex: sur "www.ma-boulangerie.fr", on garde
     "contact@maboulangerie.fr" mais on rejette "pub@gmail.com" ou
     "toto@wixpress.com"). C'est cette étape de filtrage, quasi absente du
     script Python d'origine, qui explique le principal écart de résultats
     avec la version JavaScript.

  4. Si on n'a trouvé qu'un email générique (contact@, info@...) et pas
     d'email nominatif : on cherche un numéro SIREN/SIRET dans les pages
     déjà visitées, on interroge l'API officielle et gratuite
     recherche-entreprises.api.gouv.fr pour récupérer le prénom/nom du
     dirigeant.

  5. Une fois qu'on a un prénom/nom : on reprend EXACTEMENT la logique de
     revalider_emails_pattern.py pour générer les 8 formats candidats
     (prenom.nom, prenomnom, p.nom, pnom, nom.prenom, prenom_nom, nom,
     prenom) et les VALIDER un par un par SMTP (résolution MX, détection
     catch-all, RCPT TO), jusqu'à trouver un format confirmé "Valide (SMTP
     250)" ou épuiser la liste. Même niveau de confiance (Élevé / Très
     faible / Indéterminé) que dans ce script.

Entrée  : un CSV avec une colonne contenant l'URL du site (ex: "url",
          "site web", "site", "lien"...).
Sortie  : un CSV avec, pour chaque site, les e-mails trouvés, les réseaux
          sociaux, le dirigeant trouvé (le cas échéant), l'email nominatif
          validé par SMTP et son niveau de confiance.

Usage :
    python3 trouver_emails_sites.py

Réglages tout en haut du fichier (INPUT_FILE, OUTPUT_FILE, ...).
"""

import csv
import os
import re
import socket
import smtplib
import time
import random
import unicodedata
import uuid
from urllib.parse import urlparse, urljoin

import requests
import dns.resolver

# --------------------------------------------------------------------------
# RÉGLAGES
# --------------------------------------------------------------------------

INPUT_FILE = "liste_sites.csv"          # doit contenir une colonne "url"/"site web"/...
OUTPUT_FILE = "emails_trouves.csv"

# Nombre max de sites traités en une seule exécution (0 ou vide = pas de
# limite). Permet de tourner par petits lots successifs dans GitHub Actions
# (voir trouver-emails.yml), pour rester sous la limite de temps d'un job et
# ne pas se faire bloquer par les serveurs visités à force d'enchaîner trop
# de sites d'affilée depuis la même IP. La progression est sauvegardée ligne
# par ligne (colonne "Status" = "Traité" dans liste_sites.csv), donc une
# reprise ultérieure repart automatiquement là où on s'était arrêté.
MAX_SITES_PAR_RUN = int(os.environ.get("MAX_SITES_PAR_RUN", "0") or "0")

# Pause aléatoire (en secondes) entre deux sites, pour rester poli avec les
# serveurs visités. Mets (0, 0) pour désactiver.
PAUSE_ENTRE_SITES = (0.5, 1.5)

# Nombre max de liens secondaires visités par site (comme .slice(0, 3) en JS)
MAX_LIENS_SECONDAIRES = 3

# Si True : quand aucun email nominatif n'est trouvé, on tente de déduire le
# nom du dirigeant via le SIREN/SIRET repéré sur le site (API gratuite
# recherche-entreprises.api.gouv.fr), puis on génère des candidats.
ACTIVER_RECHERCHE_DIRIGEANT = True

# Si True : les candidats générés pour le dirigeant sont validés par SMTP
# (comme dans revalider_emails_pattern.py). Si False, on génère juste le
# candidat le plus probable ("prenom.nom") sans le tester.
ACTIVER_VALIDATION_SMTP = True

# Petite pause entre deux tests SMTP consécutifs, pour rester "poli" avec
# les serveurs mail (reprise de revalider_emails_pattern.py).
PAUSE_ENTRE_VERIFICATIONS_SMTP = 0.3

# Préfixes considérés comme "génériques" (pas une personne) : contact@,
# info@... Tout email qui ne matche pas un de ces préfixes est considéré
# comme potentiellement nominatif.
PREFIXES_GENERIQUES = {
    'contact', 'info', 'infos', 'hello', 'bonjour', 'admin', 'administration',
    'accueil', 'support', 'sales', 'commercial', 'rh', 'recrutement',
    'recrutements', 'direction', 'secretariat', 'contactez-nous', 'contactezvous',
    'communication', 'presse', 'marketing', 'compta', 'comptabilite', 'facturation',
    'noreply', 'no-reply', 'newsletter', 'webmaster', 'reservation', 'reservations',
    'booking', 'boutique', 'shop', 'service-client', 'servicesclient', 'sav',
}

TIMEOUT_REQUETE = 10  # secondes

USER_AGENT = "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/124.0 Safari/537.36"

# --------------------------------------------------------------------------
# REGEX (mêmes idées que la version JavaScript)
# --------------------------------------------------------------------------

EMAIL_REGEX = re.compile(r'[a-zA-Z0-9._%+\-]+@[a-zA-Z0-9.\-]+\.[a-zA-Z]{2,}')
RESEAUX_SOCIAUX_REGEX = re.compile(
    r'href=["\'](https?://(?:www\.)?(?:facebook|instagram)\.com/[^"\']+)["\']',
    flags=re.IGNORECASE
)
LIENS_SECONDAIRES_REGEX = re.compile(
    r'href=["\']([^"\']*(?:contact|about|propos|mention|legal|cgv|equipe|team|staff)[^"\']*)["\']',
    flags=re.IGNORECASE
)

EXTENSIONS_FICHIERS_A_EXCLURE = (
    '.png', '.jpg', '.jpeg', '.gif', '.webp', '.svg', '.css', '.js',
    '.woff', '.woff2', '.ttf', '.eot', '.ico'
)

# SIREN (9 chiffres) / SIRET (14 chiffres), avec espaces optionnels tous les
# 3 chiffres comme on les trouve souvent affichés sur un site
SIREN_REGEX = re.compile(r'\b\d{3}[ \u00A0]?\d{3}[ \u00A0]?\d{3}\b')
SIRET_REGEX = re.compile(r'\b\d{3}[ \u00A0]?\d{3}[ \u00A0]?\d{3}[ \u00A0]?\d{5}\b')


# --------------------------------------------------------------------------
# OUTILS
# --------------------------------------------------------------------------

def recuperer_contenu_web(url):
    """Télécharge le HTML d'une page. Retourne "" en cas d'échec (jamais
    d'exception qui remonte), pour ne jamais bloquer le traitement des
    autres sites."""
    try:
        reponse = requests.get(
            url,
            headers={"User-Agent": USER_AGENT},
            timeout=TIMEOUT_REQUETE,
            allow_redirects=True,
        )
        # on ne filtre pas sur le status code : certains sites renvoient
        # quand même une page utilisable avec un code inhabituel
        reponse.encoding = reponse.apparent_encoding or reponse.encoding
        return reponse.text
    except Exception:
        return ""


def extraire_racine_domaine(url):
    """'https://www.ma-boulangerie.fr/contact' -> 'ma-boulangerie'
    (équivalent de extraireRacineDomaine() en JS)."""
    try:
        domaine_complet = urlparse(url).netloc.lower()
    except Exception:
        return ""
    domaine_complet = domaine_complet[4:] if domaine_complet.startswith("www.") else domaine_complet
    parts = domaine_complet.split('.')
    return parts[-2] if len(parts) > 1 else (parts[0] if parts else "")


def analyser_code_pour_emails(code_html, domaine_racine):
    """Extrait les emails du HTML puis ne garde que ceux dont le domaine
    contient un des mots-clés du nom de domaine du site (équivalent de
    analyserCodePourEmails() en JS). C'est ce filtrage qui élimine les
    adresses génériques @gmail.com, les emails d'autres sociétés glanés
    sur une page, les fausses détections type image@2x.png, etc."""
    if not code_html:
        return []

    trouves = set(EMAIL_REGEX.findall(code_html))
    resultat = []

    mots_cles = [m for m in re.split(r'[-_]', domaine_racine) if len(m) > 2]

    for email in trouves:
        email = email.lower()
        if email.endswith(EXTENSIONS_FICHIERS_A_EXCLURE):
            continue
        if '@' not in email:
            continue
        extension_email = email.split('@')[1]

        if mots_cles:
            if any(mot in extension_email for mot in mots_cles):
                resultat.append(email)
        else:
            # pas de mot-clé exploitable (nom de domaine trop court/numérique)
            # -> on garde quand même l'email pour ne pas tout perdre
            resultat.append(email)

    return sorted(set(resultat))


def analyser_code_pour_rs(code_html):
    """Liens Facebook/Instagram trouvés sur la page."""
    if not code_html:
        return []
    return sorted(set(RESEAUX_SOCIAUX_REGEX.findall(code_html)))


def extraire_liens_secondaires(code_html, url_racine):
    """Repère les liens du type contact/à-propos/mentions-légales/CGV et les
    transforme en URLs absolues (équivalent de extraireLiensSecondaires() en
    JS)."""
    if not code_html:
        return []

    liens = set()
    for lien in LIENS_SECONDAIRES_REGEX.findall(code_html):
        if lien.startswith('mailto:') or lien.startswith('tel:') or lien.startswith('javascript:'):
            continue
        lien_absolu = urljoin(url_racine, lien)
        liens.add(lien_absolu)

    return list(liens)[:MAX_LIENS_SECONDAIRES]


def formater_url(url):
    """Ajoute https:// si absent, comme demandé par requests."""
    url = (url or "").strip()
    if not url:
        return ""
    if not re.match(r'^https?://', url, flags=re.IGNORECASE):
        url = "https://" + url
    return url


def clean_string(text):
    """Minuscule, sans accents ni espaces/ponctuation - pour construire la
    partie locale d'un email à partir d'un prénom/nom."""
    if not text:
        return ""
    text = text.strip().lower()
    text = "".join(c for c in unicodedata.normalize('NFD', text) if unicodedata.category(c) != 'Mn')
    return re.sub(r'[^a-z0-9]', '', text)


def extraire_texte_pur(html):
    """Retire scripts/styles/balises - pour chercher des numéros SIREN/SIRET
    dans le texte visible de la page (équivalent extraireTextePur() en JS)."""
    if not html:
        return ""
    html = re.sub(r'<script[^>]*>[\s\S]*?</script>', ' ', html, flags=re.IGNORECASE)
    html = re.sub(r'<style[^>]*>[\s\S]*?</style>', ' ', html, flags=re.IGNORECASE)
    return re.sub(r'<[^>]+>', ' ', html)


def chercher_siren_siret(texte):
    """Retourne (siren, siret) trouvés dans le texte, ou (None, None).
    Comme en JS : on retire des candidats SIREN ceux qui ne sont en fait que
    le début d'un SIRET déjà détecté, pour éviter les doublons."""
    sirets = sorted(set(m.strip() for m in SIRET_REGEX.findall(texte)))
    sirens = sorted(set(m.strip() for m in SIREN_REGEX.findall(texte)))

    sirens = [
        s for s in sirens
        if not any(siret.replace(' ', '').replace('\u00A0', '').startswith(s.replace(' ', '').replace('\u00A0', ''))
                   for siret in sirets)
    ]

    siren = sirens[0].replace(' ', '').replace('\u00A0', '') if sirens else None
    siret = sirets[0].replace(' ', '').replace('\u00A0', '') if sirets else None
    if not siren and siret:
        siren = siret[:9]

    return siren, siret


def rechercher_dirigeants(siren):
    """Interroge l'API officielle et gratuite recherche-entreprises.api.gouv.fr
    (Annuaire des Entreprises / data.gouv.fr) pour récupérer le(s) nom(s) du
    ou des dirigeant(s) associés à un SIREN. Retourne une liste de tuples
    (prenom, nom) - seulement pour les personnes physiques (on ignore les
    dirigeants "personne morale", une autre société, dont on ne peut pas
    déduire un email nominatif)."""
    try:
        reponse = requests.get(
            "https://recherche-entreprises.api.gouv.fr/search",
            params={"q": siren},
            headers={"User-Agent": "Recherche-Emails-Crawling/1.0"},
            timeout=8,
        )
        if reponse.status_code != 200:
            return []
        data = reponse.json()
        resultats = data.get("results") or []
        if not resultats:
            return []
        dirigeants = resultats[0].get("dirigeants") or []
    except Exception:
        return []

    personnes = []
    for d in dirigeants:
        if d.get("type_dirigeant") == "personne physique":
            prenom = (d.get("prenoms") or "").split(" ")[0].strip().capitalize()
            nom = (d.get("nom") or "").strip()
            if prenom and nom:
                personnes.append((prenom, nom))
    return personnes


def detecter_pattern_email(local_part):
    """Déduit la structure d'un email nominatif déjà trouvé sur le site
    (ex: 'j.dupont' -> 'initiale.nom', 'julie.dupont' -> 'prenom.nom').
    Ne traite que les formats avec séparateur explicite ('.', '_', '-')."""
    local = local_part.lower()
    for sep in ['.', '_', '-']:
        if sep in local:
            parts = local.split(sep)
            if len(parts) == 2 and all(re.fullmatch(r'[a-z]+', p) for p in parts):
                a, b = parts
                if len(a) == 1 and len(b) > 1:
                    return f'initiale{sep}nom'
                if len(b) == 1 and len(a) > 1:
                    return f'prenom{sep}initiale'
                if len(a) > 1 and len(b) > 1:
                    return f'prenom{sep}nom'
    return None


def generer_email_depuis_pattern(prenom, nom, domaine, pattern):
    """Construit un email à partir d'un prénom/nom/domaine selon un pattern
    donné ('prenom.nom', 'initiale_nom', ...). Utilisé uniquement pour
    documenter le pattern détecté sur un email nominatif déjà présent sur le
    site (voir 'pattern_source'). La génération + validation des candidats
    pour un dirigeant trouvé via SIREN utilise generer_patterns_emails()
    ci-dessous, reprise de revalider_emails_pattern.py."""
    p = clean_string(prenom)
    n = clean_string(nom)
    if not p or not n:
        return None

    pattern = pattern or 'prenom.nom'
    formats = {
        'prenom.nom': f"{p}.{n}", 'prenom_nom': f"{p}_{n}", 'prenom-nom': f"{p}-{n}",
        'initiale.nom': f"{p[0]}.{n}", 'initiale_nom': f"{p[0]}_{n}", 'initiale-nom': f"{p[0]}-{n}",
        'prenom.initiale': f"{p}.{n[0]}", 'prenom_initiale': f"{p}_{n[0]}", 'prenom-initiale': f"{p}-{n[0]}",
    }
    local_part = formats.get(pattern, f"{p}.{n}")
    return f"{local_part}@{domaine}"


# --------------------------------------------------------------------------
# GÉNÉRATION DE PATTERNS + VALIDATION SMTP
# (reprises À L'IDENTIQUE de revalider_emails_pattern.py)
# --------------------------------------------------------------------------

def generer_patterns_emails(prenom, nom, domaine):
    """Génère une liste ordonnée (du plus probable au moins probable) de formats
    d'e-mail professionnels courants. Retourne une liste de tuples (label, email).
    Reprise à l'identique de la logique déjà validée dans enrichissement_leads.py."""
    p = clean_string(prenom)
    n = clean_string(nom).replace(" ", "")

    candidats = []
    if p and n:
        candidats.append(("prenom.nom", f"{p}.{n}@{domaine}"))
        candidats.append(("prenomnom", f"{p}{n}@{domaine}"))
        candidats.append(("p.nom", f"{p[0]}.{n}@{domaine}"))
        candidats.append(("pnom", f"{p[0]}{n}@{domaine}"))
        candidats.append(("nom.prenom", f"{n}.{p}@{domaine}"))
        candidats.append(("prenom_nom", f"{p}_{n}@{domaine}"))
        candidats.append(("nom", f"{n}@{domaine}"))
    if p:
        candidats.append(("prenom", f"{p}@{domaine}"))

    vus = set()
    resultat = []
    for label, email in candidats:
        if email and email not in vus:
            vus.add(email)
            resultat.append((label, email))
    return resultat


def get_mx_record(domaine):
    """Résout le VRAI serveur mail (enregistrement MX) du domaine. Essaie d'abord
    des résolveurs publics (Google/Cloudflare), puis se replie sur le résolveur
    système par défaut. Reprise à l'identique de la version déjà validée."""
    tentatives = [
        ("résolveurs publics (8.8.8.8 / 1.1.1.1)", ['8.8.8.8', '1.1.1.1']),
        ("résolveur système par défaut", None),
    ]
    for nom_tentative, nameservers in tentatives:
        try:
            resolver = dns.resolver.Resolver()
            if nameservers:
                resolver.nameservers = nameservers
            resolver.timeout = 5
            resolver.lifetime = 8
            records = resolver.resolve(domaine, 'MX')
            mx = str(sorted(records, key=lambda r: r.preference)[0].exchange).rstrip('.')
            return mx, None
        except dns.resolver.NXDOMAIN:
            return None, "Domaine introuvable (NXDOMAIN)"
        except dns.resolver.NoAnswer:
            return None, "Le domaine existe mais n'a aucun enregistrement MX"
        except Exception:
            continue
    return None, "Échec DNS via toutes les méthodes (blocage réseau probable)"


def ping_smtp(email, mx_server):
    """Se connecte au VRAI serveur mail (mx_server) - avec expéditeur MAIL FROM:<>
    (null, conforme RFC 5321) plutôt qu'un domaine expéditeur inventé. Reprise à
    l'identique de la version déjà corrigée et validée."""
    if not mx_server:
        return "Impossible (aucun serveur MX résolu pour ce domaine)"

    try:
        server = smtplib.SMTP(timeout=8)
        server.connect(mx_server, 25)
        server.helo("verification-bot.com")

        code_expediteur, msg_expediteur = server.mail("")
        if code_expediteur not in (250, 251):
            server.quit()
            msg_txt = msg_expediteur.decode(errors='ignore') if isinstance(msg_expediteur, bytes) else msg_expediteur
            return f"Expéditeur rejeté par le serveur (code {code_expediteur} : {msg_txt}) - vérification impossible"

        code, message = server.rcpt(email)
        server.quit()

        if code == 250:
            return "Valide (SMTP 250)"
        elif code == 550:
            return "Inexistant (SMTP 550)"
        else:
            return f"Incertain (Code {code} : {message.decode(errors='ignore') if isinstance(message, bytes) else message})"

    except (socket.timeout, TimeoutError):
        return "Timeout (le port 25 est probablement bloqué par votre réseau/hébergeur)"
    except ConnectionRefusedError:
        return "Connexion refusée (port 25 fermé côté serveur cible ou bloqué par votre réseau)"
    except smtplib.SMTPServerDisconnected:
        return "Le serveur a coupé la connexion (blocage anti-spam probable côté entreprise)"
    except smtplib.SMTPResponseException as e:
        return f"Rejet SMTP explicite (code {e.smtp_code})"
    except OSError as e:
        return f"Erreur réseau : {e}"
    except Exception as e:
        return f"Échec inattendu ({type(e).__name__})"


def detecter_catch_all_smtp(domaine, mx_server):
    """Teste si le serveur mail du domaine accepte n'importe quelle adresse
    (mode 'catch-all'). Reprise à l'identique."""
    faux_local_part = f"verif-inexistante-{uuid.uuid4().hex[:10]}"
    resultat = ping_smtp(f"{faux_local_part}@{domaine}", mx_server)
    return resultat == "Valide (SMTP 250)"


def calculer_niveau_confiance(email_valide_trouve, mx_server):
    """Calcule un niveau de confiance à partir de ce que le SMTP a pu confirmer.
    Reprise à l'identique de revalider_emails_pattern.py :
    - Élevé : un format a été confirmé positivement par SMTP
    - Très faible : vérification tentée (MX résolu) mais rien de confirmé
      (catch-all, ou tous les formats rejetés/incertains)
    - Indéterminé : la résolution MX elle-même a échoué"""
    if not mx_server:
        return "Indéterminé"
    if email_valide_trouve:
        return "Élevé"
    return "Très faible"


def valider_candidats_par_smtp(prenom, nom, domaine, cache_mx, cache_catch_all):
    """Génère les candidats (generer_patterns_emails) puis les valide par SMTP,
    exactement comme revalider_emails_pattern.py : résolution MX (mise en cache
    par domaine), détection catch-all (mise en cache), puis test des formats un
    par un jusqu'à trouver un "Valide (SMTP 250)".

    cache_mx et cache_catch_all sont des dicts partagés entre tous les sites du
    run, pour ne résoudre/tester chaque domaine qu'une seule fois."""
    candidats = generer_patterns_emails(prenom, nom, domaine)

    resultat = {
        "email_nominatif_genere": candidats[0][1] if candidats else "",
        "resultat_smtp": "", "serveur_mx": "", "catch_all": "",
        "nb_formats_testes": 0, "niveau_confiance": "Indéterminé",
    }
    if not candidats:
        return resultat

    if domaine not in cache_mx:
        mx_server, _erreur_mx = get_mx_record(domaine)
        cache_mx[domaine] = mx_server
    mx_server = cache_mx[domaine]
    resultat["serveur_mx"] = mx_server or ""

    if not mx_server:
        resultat["resultat_smtp"] = "Impossible (résolution MX échouée)"
        resultat["niveau_confiance"] = calculer_niveau_confiance("", mx_server)
        return resultat

    if domaine not in cache_catch_all:
        cache_catch_all[domaine] = detecter_catch_all_smtp(domaine, mx_server)
        time.sleep(PAUSE_ENTRE_VERIFICATIONS_SMTP)
    resultat["catch_all"] = "Oui" if cache_catch_all[domaine] else "Non"

    if cache_catch_all[domaine]:
        resultat["resultat_smtp"] = "Catch-all confirmé (aucun format vérifiable par SMTP)"
        resultat["niveau_confiance"] = calculer_niveau_confiance("", mx_server)
        return resultat

    email_valide = ""
    for label, email in candidats:
        r = ping_smtp(email, mx_server)
        resultat["nb_formats_testes"] += 1
        print(f"        [{label}] {email} -> {r}")
        if r == "Valide (SMTP 250)":
            email_valide = email
            resultat["resultat_smtp"] = r
            break
        time.sleep(PAUSE_ENTRE_VERIFICATIONS_SMTP)

    if email_valide:
        resultat["email_nominatif_genere"] = email_valide
    else:
        resultat["resultat_smtp"] = "Aucun format validé par SMTP"

    resultat["niveau_confiance"] = calculer_niveau_confiance(email_valide, mx_server)
    return resultat


def classer_emails(emails):
    """Sépare les emails trouvés en (génériques, nominatifs) selon leur
    préfixe (avant le @)."""
    generiques, nominatifs = [], []
    for email in emails:
        prefixe = email.split('@')[0].lower()
        if prefixe in PREFIXES_GENERIQUES:
            generiques.append(email)
        else:
            nominatifs.append(email)
    return generiques, nominatifs


def trouver_colonne_url(fieldnames):
    """Devine quelle colonne du CSV contient l'URL du site."""
    candidats = ["url", "site web", "site_web", "site", "lien", "website", "web"]
    for nom_col in fieldnames:
        if nom_col.strip().lower() in candidats:
            return nom_col
    # repli : première colonne
    return fieldnames[0]


def trouver_colonne_status(fieldnames):
    """Devine quelle colonne du CSV sert à suivre la progression (comme dans
    enrichissement_leads.py / verifier_emails_smtp.py)."""
    candidats = ["status", "statut", "statut de traitement", "traite"]
    for nom_col in fieldnames:
        if nom_col.strip().lower() in candidats:
            return nom_col
    return None


# --------------------------------------------------------------------------
# TRAITEMENT D'UN SEUL SITE
# --------------------------------------------------------------------------

def trouver_emails_pour_site(url_site, cache_mx, cache_catch_all):
    """Traite un site : page d'accueil + liens secondaires, cumule les
    résultats.

    Retourne un dict :
      emails, reseaux_sociaux, domaine (nom de domaine réel du site),
      dirigeant_trouve, pattern_source,
      email_nominatif_genere, resultat_smtp, serveur_mx, catch_all,
      nb_formats_testes, niveau_confiance
    """
    resultat = {
        "emails": [], "reseaux_sociaux": [], "domaine": "",
        "dirigeant_trouve": "", "pattern_source": "",
        "email_nominatif_genere": "", "resultat_smtp": "",
        "serveur_mx": "", "catch_all": "", "nb_formats_testes": 0,
        "niveau_confiance": "",
    }

    url_site = formater_url(url_site)
    if not url_site:
        return resultat

    domaine_racine = extraire_racine_domaine(url_site)
    domaine_reel = urlparse(url_site).netloc.lower()
    domaine_reel = domaine_reel[4:] if domaine_reel.startswith("www.") else domaine_reel
    resultat["domaine"] = domaine_reel

    # On visite systématiquement l'accueil + les liens secondaires (contact,
    # équipe, mentions légales...) pour maximiser les chances de tomber sur
    # un email nominatif ou un SIREN, même si un email générique a déjà été
    # trouvé sur l'accueil - contrairement à la version précédente qui
    # s'arrêtait dès le premier email trouvé.
    pages_html = [recuperer_contenu_web(url_site)]
    liens_secondaires = extraire_liens_secondaires(pages_html[0], url_site)
    for lien in liens_secondaires:
        pages_html.append(recuperer_contenu_web(lien))

    emails = set()
    reseaux_sociaux = set()
    texte_complet = ""
    for html in pages_html:
        emails |= set(analyser_code_pour_emails(html, domaine_racine))
        reseaux_sociaux |= set(analyser_code_pour_rs(html))
        texte_complet += " " + extraire_texte_pur(html)

    resultat["emails"] = sorted(emails)
    resultat["reseaux_sociaux"] = sorted(reseaux_sociaux)

    if not ACTIVER_RECHERCHE_DIRIGEANT:
        return resultat

    generiques, nominatifs = classer_emails(resultat["emails"])

    if nominatifs:
        # On a déjà au moins un email nominatif réel : pas besoin de générer
        # quoi que ce soit, mais on garde le pattern pour information.
        pattern = detecter_pattern_email(nominatifs[0].split('@')[0])
        resultat["pattern_source"] = f"email nominatif déjà trouvé sur le site ({pattern or 'format non identifié'})"
        return resultat

    if not generiques:
        # Aucun email du tout trouvé sur le site : pas de domaine confirmé
        # à exploiter pour deviner quoi que ce soit d'utile.
        return resultat

    # Cas visé par la demande : uniquement un/des email(s) générique(s).
    # On récupère le domaine confirmé depuis cet email générique.
    domaine_confirme = generiques[0].split('@')[1]

    siren, siret = chercher_siren_siret(texte_complet)
    if not siren:
        return resultat

    dirigeants = rechercher_dirigeants(siren)
    if not dirigeants:
        return resultat

    prenom, nom = dirigeants[0]
    resultat["dirigeant_trouve"] = f"{prenom} {nom}"
    resultat["pattern_source"] = f"dirigeant trouvé via SIREN {siren} (API recherche-entreprises.api.gouv.fr)"

    if ACTIVER_VALIDATION_SMTP:
        print(f"    -> dirigeant '{prenom} {nom}' trouvé, validation SMTP des formats possibles sur {domaine_confirme}...")
        smtp_info = valider_candidats_par_smtp(prenom, nom, domaine_confirme, cache_mx, cache_catch_all)
        resultat.update(smtp_info)
    else:
        resultat["email_nominatif_genere"] = generer_email_depuis_pattern(prenom, nom, domaine_confirme, pattern=None)

    return resultat


# --------------------------------------------------------------------------
# BOUCLE PRINCIPALE
# --------------------------------------------------------------------------

def executer():
    if not os.path.exists(INPUT_FILE):
        print(f"Fichier introuvable : {INPUT_FILE}")
        return 0

    with open(INPUT_FILE, mode='r', newline='', encoding='utf-8-sig') as f_in:
        # détection simple du séparateur (virgule ou point-virgule)
        premiere_ligne = f_in.readline()
        f_in.seek(0)
        delimiteur = ';' if premiere_ligne.count(';') > premiere_ligne.count(',') else ','
        reader = csv.DictReader(f_in, delimiter=delimiteur)
        fieldnames = reader.fieldnames or []
        lignes = list(reader)

    if not fieldnames:
        print("CSV vide ou illisible.")
        return 0

    colonne_url = trouver_colonne_url(fieldnames)
    print(f"Colonne URL détectée : '{colonne_url}'")

    # Colonne de suivi de progression - créée si absente, comme dans les
    # autres scripts du projet (enrichissement_leads.py, verifier_emails_smtp.py).
    colonne_status = trouver_colonne_status(fieldnames)
    if not colonne_status:
        colonne_status = "Status"
        fieldnames.append(colonne_status)
        for ligne in lignes:
            ligne[colonne_status] = ""

    def sauvegarder_progression():
        """Réécrit INPUT_FILE avec l'état à jour de la colonne Status, pour
        qu'une reprise ultérieure (nouveau run GitHub Actions) saute
        automatiquement les lignes déjà traitées."""
        with open(INPUT_FILE, mode='w', newline='', encoding='utf-8') as f_in:
            writer = csv.DictWriter(f_in, fieldnames=fieldnames, delimiter=delimiteur)
            writer.writeheader()
            writer.writerows(lignes)

    colonnes_sortie = fieldnames + [
        "Emails trouvés", "Réseaux sociaux",
        "Dirigeant trouvé", "Source du pattern",
        "Email nominatif généré", "Résultat SMTP", "Serveur MX", "Catch-all",
        "Nb formats testés", "Niveau de confiance",
    ]
    ecrire_entete = not os.path.exists(OUTPUT_FILE) or os.path.getsize(OUTPUT_FILE) == 0

    cache_mx = {}
    cache_catch_all = {}

    nb_traitees = 0
    nb_ignorees_status = 0
    nb_ignorees_url_vide = 0

    with open(OUTPUT_FILE, mode='a', newline='', encoding='utf-8') as f_out:
        writer = csv.DictWriter(f_out, fieldnames=colonnes_sortie, delimiter=';')
        if ecrire_entete:
            writer.writeheader()

        total = len(lignes)
        for i, ligne in enumerate(lignes, start=1):
            statut_actuel = (ligne.get(colonne_status) or "").strip().lower()
            if statut_actuel in ("traite", "traité"):
                nb_ignorees_status += 1
                continue

            url_site = (ligne.get(colonne_url) or "").strip()

            if not url_site:
                nb_ignorees_url_vide += 1
                ligne[colonne_status] = "Traité"
                sauvegarder_progression()
                continue

            print(f"[{i}/{total}] {url_site}")

            champs_vides = {
                "Emails trouvés": "", "Réseaux sociaux": "",
                "Dirigeant trouvé": "", "Source du pattern": "",
                "Email nominatif généré": "", "Résultat SMTP": "", "Serveur MX": "",
                "Catch-all": "", "Nb formats testés": "", "Niveau de confiance": "",
            }

            try:
                r = trouver_emails_pour_site(url_site, cache_mx, cache_catch_all)
            except Exception as e:
                print(f"    -> erreur : {e}")
                r = dict.fromkeys(champs_vides, "")
                r["emails"], r["reseaux_sociaux"] = [], []

            print(f"    -> emails : {r['emails'] if r['emails'] else 'aucun'}")
            if r.get("dirigeant_trouve"):
                print(f"    -> dirigeant trouvé : {r['dirigeant_trouve']} "
                      f"-> email : {r.get('email_nominatif_genere') or '(aucun format généré)'} "
                      f"[{r.get('niveau_confiance')}]")

            ligne_sortie = dict(ligne)
            ligne_sortie["Emails trouvés"] = ", ".join(r["emails"])
            ligne_sortie["Réseaux sociaux"] = ", ".join(r["reseaux_sociaux"])
            ligne_sortie["Dirigeant trouvé"] = r.get("dirigeant_trouve", "")
            ligne_sortie["Source du pattern"] = r.get("pattern_source", "")
            ligne_sortie["Email nominatif généré"] = r.get("email_nominatif_genere", "")
            ligne_sortie["Résultat SMTP"] = r.get("resultat_smtp", "")
            ligne_sortie["Serveur MX"] = r.get("serveur_mx", "")
            ligne_sortie["Catch-all"] = r.get("catch_all", "")
            ligne_sortie["Nb formats testés"] = r.get("nb_formats_testes", "")
            ligne_sortie["Niveau de confiance"] = r.get("niveau_confiance", "")
            writer.writerow(ligne_sortie)
            f_out.flush()

            nb_traitees += 1

            # Sauvegarde en temps réel : même si le job est interrompu (timeout
            # GitHub Actions, coupure réseau...), la progression déjà faite
            # n'est jamais perdue.
            ligne[colonne_status] = "Traité"
            sauvegarder_progression()

            # Limite de lot atteinte : on s'arrête proprement ici pour laisser
            # la main à l'orchestrateur (workflow GitHub Actions), qui
            # relancera un nouveau lot si besoin.
            if MAX_SITES_PAR_RUN and nb_traitees >= MAX_SITES_PAR_RUN:
                print(f"\n--- Limite de {MAX_SITES_PAR_RUN} site(s) par exécution atteinte ---")
                break

            time.sleep(random.uniform(*PAUSE_ENTRE_SITES))

    lignes_restantes = 0
    for ligne in lignes:
        url_verif = (ligne.get(colonne_url) or "").strip()
        statut_verif = (ligne.get(colonne_status) or "").strip().lower()
        if url_verif and statut_verif not in ("traite", "traité"):
            lignes_restantes += 1

    print("\n--- Résumé ---")
    print(f"Sites traités (cette exécution) : {nb_traitees}")
    print(f"Ignorés (déjà 'Traité') : {nb_ignorees_status}")
    print(f"Ignorés (pas d'URL) : {nb_ignorees_url_vide}")
    print(f"Lignes restant à traiter : {lignes_restantes}")
    print(f"Terminé. Résultats écrits dans : {OUTPUT_FILE}")

    return lignes_restantes


if __name__ == "__main__":
    restantes = executer()
    # Code de sortie 2 = il reste du travail (le workflow GitHub Actions
    # relance alors automatiquement un nouveau lot). Code 0 = tout est terminé.
    if restantes:
        raise SystemExit(2)
