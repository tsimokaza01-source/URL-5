import csv
import os
import re
import subprocess
import time
import unicodedata
import requests
from urllib.parse import urlparse, urljoin, unquote

# ==================== CONFIGURATION ====================
INPUT_FILE = "liste_hotels.csv"
OUTPUT_FILE = "hotels_enrichis.csv"

# Nombre max d'hôtels traités en une seule exécution (0 = pas de limite).
MAX_HOTELS_PAR_RUN = int(os.environ.get("MAX_HOTELS_PAR_RUN", "0") or "0")

# Timeout HTTP par page visitée (secondes) - réduit pour éviter qu'un site lent
# ou hors-ligne ne ralentisse tout le lot.
TIMEOUT_HTTP = float(os.environ.get("TIMEOUT_HTTP", "6") or "6")

# Enregistrement en temps réel : si activé (mettre "1" dans le workflow CI),
# le script fait un `git add/commit/push` après chaque hôtel traité (ou tous
# les N hôtels via COMMIT_TOUTES_LES), au lieu d'attendre la fin du lot.
# Désactivé par défaut pour ne rien casser en exécution locale.
COMMIT_TEMPS_REEL = os.environ.get("COMMIT_TEMPS_REEL", "0") == "1"
COMMIT_TOUTES_LES = max(1, int(os.environ.get("COMMIT_TOUTES_LES", "1") or "1"))

PREFIXES_GENERIQUES = {
    'contact', 'info', 'hello', 'bonjour', 'commercial', 'office', 'support',
    'sales', 'reservation', 'reservations', 'booking', 'reception', 'accueil',
    'hr', 'rh', 'recrutement', 'jobs', 'careers', 'presse', 'press',
    'marketing', 'admin', 'webmaster', 'noreply', 'no-reply', 'contactez'
}
# =======================================================


def corriger_mojibake(text):
    """Répare les accents cassés (ex: 'AnaÃ¯s' -> 'Anaïs')."""
    if not text or ("Ã" not in text and "â€" not in text):
        return text
    try:
        return text.encode('cp1252').decode('utf-8')
    except (UnicodeDecodeError, UnicodeEncodeError):
        return text


def extraire_domaine_depuis_site_web(url):
    """Extrait le domaine propre à partir d'une URL de site web fournie."""
    if not url:
        return None
    url = url.strip()
    if not url:
        return None
    if not re.match(r'^https?://', url, flags=re.IGNORECASE):
        url = "https://" + url
    try:
        domaine = urlparse(url).netloc
    except ValueError:
        return None
    domaine = domaine.split('@')[-1].split(':')[0]
    domaine = re.sub(r'^www\.', '', domaine, flags=re.IGNORECASE)
    return domaine.strip('/').lower() or None


def domaines_lies(domaine_original, domaine_trouve):
    """Vérifie que le domaine trouvé (ex: d'un email) est plausiblement lié au
    domaine du site d'origine avant de l'accepter (ex: 'monhotel' dans
    'monhotel-group.com' -> OK, un domaine totalement étranger -> refusé)."""
    if not domaine_original or not domaine_trouve:
        return False
    if domaine_original.lower() == domaine_trouve.lower():
        return True
    nom_principal = domaine_original.split('.')[0].lower()
    if len(nom_principal) <= 2:
        return nom_principal == domaine_trouve.split('.')[0].lower()
    return nom_principal in domaine_trouve.lower()


def determiner_delimiteur(filepath, encodage):
    with open(filepath, mode='r', newline='', encoding=encodage) as f:
        premiere_ligne = f.readline()
        echantillon = premiere_ligne + f.readline()
    candidats = [',', ';', '\t', '|']
    comptes = {c: premiere_ligne.count(c) for c in candidats}
    meilleur = max(comptes, key=comptes.get)
    if comptes[meilleur] > 0:
        return meilleur
    try:
        dialecte = csv.Sniffer().sniff(echantillon, delimiters=",;\t|: ")
        return dialecte.delimiter
    except csv.Error:
        return ','


def lire_csv_avec_encodage_securise(filepath):
    encodages = ['utf-8-sig', 'utf-8', 'cp1252', 'latin1']
    derniere_erreur = None
    for encodage in encodages:
        try:
            delimiteur = determiner_delimiteur(filepath, encodage)
            with open(filepath, mode='r', newline='', encoding=encodage) as f:
                reader = csv.DictReader(f, delimiter=delimiteur)
                lignes = list(reader)
                fieldnames = reader.fieldnames
                return lignes, fieldnames, encodage, delimiteur
        except (UnicodeDecodeError, Exception) as e:
            derniere_erreur = e
            continue
    raise UnicodeDecodeError(f"Impossible de lire le fichier. Dernière erreur : {derniere_erreur}", b"", 0, 1, "")


def trouver_valeur_colonne(ligne, mots_cles, exclure_cles=None):
    exclure_cles = exclure_cles or []
    for cle, valeur in ligne.items():
        if cle and cle not in exclure_cles and any(mot in cle.strip().lower() for mot in mots_cles):
            return cle, valeur
    return None, ""


def extraire_emails_dune_page(html):
    """Repère les adresses e-mail en clair dans une page (liens mailto: ou texte),
    en filtrant les faux positifs courants (images, CDN, trackers)."""
    if not html:
        return []
    trouve = set()
    for m in re.findall(r'mailto:([^"\'>\s?]+)', html, flags=re.IGNORECASE):
        email = m.split('?')[0].strip()
        if '@' in email:
            trouve.add(email.lower())
    for m in re.findall(r'[a-zA-Z0-9_.+-]+@[a-zA-Z0-9-]+\.[a-zA-Z0-9-.]+', html):
        trouve.add(m.lower())

    extensions_a_exclure = {'png', 'jpg', 'jpeg', 'gif', 'svg', 'webp', 'ico', 'css',
                             'js', 'woff', 'woff2', 'ttf', 'eot', 'map', 'json', 'xml', 'pdf'}
    domaines_a_exclure = {'sentry.io', 'wixpress.com', 'wix.com', 'cloudflare.com',
                           'googleapis.com', 'gstatic.com', 'schema.org', 'w3.org',
                           'godaddy.com', 'example.com', 'google.com', 'facebook.com',
                           'twitter.com', 'x.com', 'instagram.com', 'linkedin.com', 'youtube.com'}
    resultat = []
    for email in trouve:
        local, sep, dom = email.partition('@')
        if not sep or not dom or '.' not in dom:
            continue
        if dom.rsplit('.', 1)[-1] in extensions_a_exclure or dom in domaines_a_exclure:
            continue
        if len(local) > 64 or len(dom) > 253:
            continue
        resultat.append(email)
    return resultat


def extraire_liens_pertinents(html, domaine, mots_cles, limite=6):
    """Trouve dans les liens de navigation d'une page ceux qui pointent probablement
    vers une page contact/équipe/à-propos, quelle que soit la structure d'URL du site."""
    if not html:
        return []
    liens_bruts = re.findall(r'<a\s+[^>]*href=["\']([^"\']+)["\'][^>]*>(.*?)</a>',
                              html, flags=re.IGNORECASE | re.DOTALL)
    base = f"https://{domaine}"
    trouves = []
    for href, texte_html in liens_bruts:
        texte = re.sub(r'<[^<]+?>', '', texte_html).strip().lower()
        if any(mot in href.lower() or mot in texte for mot in mots_cles):
            url_absolue = urljoin(base, href)
            if domaine in urlparse(url_absolue).netloc:
                trouves.append(url_absolue)
    vus = set()
    resultat = []
    for url in trouves:
        if url not in vus:
            vus.add(url)
            resultat.append(url)
        if len(resultat) >= limite:
            break
    return resultat


def extraire_lien_linkedin_company(html, domaine):
    """Cherche un lien LinkedIn 'entreprise' (linkedin.com/company/... ou
    /showcase/...) dans une page - typiquement présent dans le footer ou header
    d'un site d'hôtel/entreprise. Retourne l'URL normalisée ou None."""
    if not html:
        return None
    matches = re.findall(
        r'https?://(?:[a-z]{2,3}\.)?linkedin\.com/(company|showcase)/([a-zA-Z0-9\-_%]+)',
        html, flags=re.IGNORECASE
    )
    if not matches:
        return None
    type_page, slug = matches[0]
    slug = unquote(slug).strip('/')
    return f"https://www.linkedin.com/{type_page.lower()}/{slug}"


def extraire_nom_pres_email(html, email):
    """Heuristique BEST-EFFORT : cherche un nom de personne dans le texte entourant
    la mention de l'email sur la page (ex: 'Contactez Jean Dupont : jean@...').
    Ce n'est PAS une garantie - beaucoup de pages n'ont pas de nom associé à
    l'email, ou ont un nom trop ambigu pour être extrait fiablement. Retourne None
    si rien de suffisamment net n'est trouvé, plutôt que de deviner au hasard."""
    if not html or not email:
        return None

    index = html.lower().find(email.lower())
    if index == -1:
        return None

    # On regarde une fenêtre de texte autour de la position de l'email (avant et après)
    fenetre = html[max(0, index - 300): index + 100]
    texte_brut = re.sub(r'<[^<]+?>', ' ', fenetre)  # retire les balises HTML
    texte_brut = re.sub(r'\s+', ' ', texte_brut).strip()

    # Motif d'un "mot" de nom : gère aussi les prénoms/noms composés avec majuscule
    # après le tiret (ex: "Jean-Pierre", "Marie-Claire").
    mot_nom = r"[A-ZÀ-Ý][a-zà-ÿ']+(?:-[A-ZÀ-Ý][a-zà-ÿ']+)*"

    mots_a_exclure = {'contactez nous', 'en savoir', 'nous contacter', 'mentions legales',
                       'politique confidentialite', 'tous droits', 'suivez nous'}

    candidats_2_mots = re.findall(rf'\b({mot_nom}\s+{mot_nom})\b', texte_brut)
    for candidat in candidats_2_mots:
        if candidat.lower() not in mots_a_exclure:
            return candidat

    candidats_3_mots = re.findall(rf'\b({mot_nom}\s+{mot_nom}\s+{mot_nom})\b', texte_brut)
    for candidat in candidats_3_mots:
        if candidat.lower() not in mots_a_exclure:
            return candidat

    return None


def committer_et_pousser(message):
    """Enregistre la progression en temps réel dans le dépôt Git (add + commit +
    push des CSV). Best-effort : n'est appelé qu'en CI (COMMIT_TEMPS_REEL=1) et
    ne doit jamais faire planter le script si git échoue (réseau, conflit...)."""
    if not COMMIT_TEMPS_REEL:
        return
    try:
        subprocess.run(["git", "add", INPUT_FILE, OUTPUT_FILE], check=True)
        resultat = subprocess.run(["git", "diff", "--cached", "--quiet"])
        if resultat.returncode == 0:
            return  # rien de nouveau à committer
        subprocess.run(["git", "commit", "-m", message], check=True)
        subprocess.run(["git", "push"], check=True)
    except Exception as e:
        print(f" ! Avertissement : échec du commit/push en temps réel ({e})")


def initialiser_fichiers():
    if not os.path.exists(OUTPUT_FILE) or os.path.getsize(OUTPUT_FILE) == 0:
        with open(OUTPUT_FILE, mode='w', newline='', encoding='utf-8') as f:
            writer = csv.writer(f)
            writer.writerow([
                "Nom_Hotel", "Adresse", "Site_Web", "Domaine",
                "LinkedIn_Company", "Source_LinkedIn",
                "Email_Trouve", "Type_Email", "Nom_Associe"
            ])


def analyser_hotel(url_site, nom_hotel=None, adresse=None):
    """Analyse un hôtel dont le site web est déjà connu : cherche sur ce site
    (page d'accueil + pages contact/équipe/à-propos) sa page LinkedIn company,
    un email générique/nominatif lié au domaine, et si pas de LinkedIn, un nom
    associé à l'email trouvé. Ne fait AUCUNE recherche web externe - se limite
    strictement au contenu du site fourni."""
    resultat = {
        'domaine': None, 'site_web': None,
        'linkedin': None, 'source_linkedin': '',
        'email': None, 'type_email': '', 'nom_associe': ''
    }

    domaine = extraire_domaine_depuis_site_web(url_site) if url_site else None

    if domaine:
        resultat['site_web'] = url_site

    resultat['domaine'] = domaine
    if not domaine:
        return resultat

    headers = {"User-Agent": "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36"}
    mots_cles_liens = ['contact', 'team', 'equipe', 'équipe', 'about', 'a-propos',
                        'propos', 'staff', 'people']

    tous_les_emails = []
    html_accueil = None
    html_pages_visitees = {}

    try:
        reponse = requests.get(f"https://{domaine}", headers=headers, timeout=TIMEOUT_HTTP)
        if reponse.status_code == 200:
            html_accueil = reponse.text
            html_pages_visitees[f"https://{domaine}"] = html_accueil
    except Exception:
        pass

    if html_accueil:
        tous_les_emails.extend(extraire_emails_dune_page(html_accueil))

    # 1. Recherche du lien LinkedIn company directement sur le site
    lien_linkedin = extraire_lien_linkedin_company(html_accueil, domaine) if html_accueil else None
    if lien_linkedin:
        resultat['linkedin'] = lien_linkedin
        resultat['source_linkedin'] = "Site propre (page d'accueil)"

    # 2. Visite des pages contact/équipe découvertes dynamiquement
    liens = extraire_liens_pertinents(html_accueil, domaine, mots_cles_liens) if html_accueil else []
    chemins_secours = [f"https://{domaine}{c}" for c in
                        ["/contact", "/contact-us", "/nous-contacter", "/about", "/a-propos"]]
    urls_a_visiter = liens + [u for u in chemins_secours if u not in liens]

    for url in urls_a_visiter:
        try:
            reponse = requests.get(url, headers=headers, timeout=TIMEOUT_HTTP)
            if reponse.status_code == 200:
                html_pages_visitees[url] = reponse.text
                tous_les_emails.extend(extraire_emails_dune_page(reponse.text))
                if not lien_linkedin:
                    lien_linkedin = extraire_lien_linkedin_company(reponse.text, domaine)
                    if lien_linkedin:
                        resultat['linkedin'] = lien_linkedin
                        resultat['source_linkedin'] = "Site propre (page contact/équipe)"
        except Exception:
            continue
        # On arrête tôt si on a déjà LinkedIn + au moins un email lié au domaine
        emails_lies = [e for e in tous_les_emails if domaines_lies(domaine, e.split('@')[-1])]
        if lien_linkedin and emails_lies:
            break

    # 3. Filtre les emails : on ne garde que ceux dont le domaine correspond ou
    #    contient une partie du nom de domaine du site (demande explicite).
    vus = set()
    emails_uniques = [e for e in tous_les_emails if not (e in vus or vus.add(e))]
    emails_lies = [e for e in emails_uniques if domaines_lies(domaine, e.split('@')[-1])]

    if emails_lies:
        # Priorité aux emails nominatifs (plus utiles), sinon générique
        nominatifs = [e for e in emails_lies if e.split('@')[0] not in PREFIXES_GENERIQUES]
        if nominatifs:
            resultat['email'] = nominatifs[0]
            resultat['type_email'] = "Nominatif"
        else:
            resultat['email'] = emails_lies[0]
            resultat['type_email'] = "Générique"

    # 4. Si toujours pas de LinkedIn : tentative d'extraction d'un nom associé à
    #    l'email trouvé, sur la page où cet email a été repéré.
    if not resultat['linkedin'] and resultat['email']:
        for url, html_page in html_pages_visitees.items():
            nom = extraire_nom_pres_email(html_page, resultat['email'])
            if nom:
                resultat['nom_associe'] = corriger_mojibake(nom)
                break

    return resultat


def executer_enrichissement_hotels():
    initialiser_fichiers()

    if not os.path.exists(INPUT_FILE):
        print(f"Erreur : Le fichier {INPUT_FILE} est introuvable dans le dossier courant : {os.getcwd()}")
        return 0

    try:
        lignes, fieldnames, encodage_detecte, delimiteur_detecte = lire_csv_avec_encodage_securise(INPUT_FILE)
        print(f"Fichier lu (Encodage: {encodage_detecte} | Séparateur: '{delimiteur_detecte}')")
        print(f"Colonnes détectées : {fieldnames}")
        print(f"Nombre de lignes lues : {len(lignes)}")
    except Exception as e:
        print(f"Erreur lors de la lecture du fichier : {e}")
        return 0

    if not lignes:
        print("Le fichier d'entrée ne contient aucune ligne de données.")
        return 0

    nb_traitees = 0
    nb_ignorees_status = 0
    nb_ignorees_vide = 0

    for index, ligne in enumerate(lignes):
        cle_site, site_brut = trouver_valeur_colonne(ligne, ["site web", "website", "url", "domaine", "site"])
        site_brut = corriger_mojibake((site_brut or "").strip())

        cle_nom, nom_brut = trouver_valeur_colonne(
            ligne, ["nom de l'hotel", "nom hotel", "hotel", "etablissement", "établissement", "nom"],
            exclure_cles=[cle_site]
        )
        nom_hotel = corriger_mojibake((nom_brut or "").strip()) or None

        cle_adresse, adresse_brute = trouver_valeur_colonne(ligne, ["adresse", "address"])
        adresse = corriger_mojibake((adresse_brute or "").strip()) or None

        cle_status, status_actuel = trouver_valeur_colonne(ligne, ["status", "statut"])
        status_actuel = (status_actuel or "").strip()

        if not cle_status:
            cle_status = "Status"
            ligne[cle_status] = ""
            if "Status" not in fieldnames:
                fieldnames.append("Status")

        if status_actuel.lower() in ["traite", "traité"]:
            nb_ignorees_status += 1
            continue

        # Le site web doit maintenant être fourni : sans recherche web, un hôtel
        # sans site connu ne peut rien apporter.
        if not site_brut:
            nb_ignorees_vide += 1
            print(f"[{index+1}/{len(lignes)}] Ignoré : pas de site web fourni sur cette ligne.")
            continue

        print(f"\n[{index+1}/{len(lignes)}] Analyse de : {nom_hotel or site_brut}")
        print(f" -> Site web fourni : {site_brut}")

        resultat = analyser_hotel(site_brut, nom_hotel, adresse)

        print(f" -> Domaine : {resultat['domaine']}")
        print(f" -> LinkedIn : {resultat['linkedin'] or 'non trouvé'} ({resultat['source_linkedin']})")
        print(f" -> Email : {resultat['email'] or 'non trouvé'} ({resultat['type_email']})")
        if resultat['nom_associe']:
            print(f" -> Nom associé : {resultat['nom_associe']}")

        with open(OUTPUT_FILE, mode='a', newline='', encoding='utf-8') as f_out:
            writer = csv.writer(f_out)
            writer.writerow([
                nom_hotel or "", adresse or "", resultat['site_web'] or "",
                resultat['domaine'] or "",
                resultat['linkedin'] or "", resultat['source_linkedin'], resultat['email'] or "",
                resultat['type_email'], resultat['nom_associe']
            ])

        nb_traitees += 1

        ligne[cle_status] = "Traité"
        with open(INPUT_FILE, mode='w', newline='', encoding=encodage_detecte) as f_in:
            writer = csv.DictWriter(f_in, fieldnames=fieldnames, delimiter=delimiteur_detecte)
            writer.writeheader()
            writer.writerows(lignes)

        # Enregistrement en temps réel dans le dépôt Git (voir COMMIT_TEMPS_REEL)
        if nb_traitees % COMMIT_TOUTES_LES == 0:
            committer_et_pousser(f"Enrichissement hotels - {nb_traitees} traite(s) dans ce lot")

        time.sleep(1.0)

        if MAX_HOTELS_PAR_RUN and nb_traitees >= MAX_HOTELS_PAR_RUN:
            print(f"\n--- Limite de {MAX_HOTELS_PAR_RUN} hôtel(s) par exécution atteinte ---")
            break

    lignes_restantes = 0
    for ligne in lignes:
        _, site_verif = trouver_valeur_colonne(ligne, ["site web", "website", "url", "domaine", "site"])
        _, status_verif = trouver_valeur_colonne(ligne, ["status", "statut"])
        a_de_quoi_traiter = (site_verif or "").strip()
        if a_de_quoi_traiter and (status_verif or "").strip().lower() not in ["traite", "traité"]:
            lignes_restantes += 1

    print("\n--- Résumé ---")
    print(f"Hôtels traités (cette exécution) : {nb_traitees}")
    print(f"Ignorés (déjà 'Traité') : {nb_ignorees_status}")
    print(f"Ignorés (pas de site web fourni) : {nb_ignorees_vide}")
    print(f"Hôtels restant à traiter : {lignes_restantes}")
    print("Fait !")

    # Commit final de sécurité (couvre le reliquat si COMMIT_TOUTES_LES > 1)
    committer_et_pousser(f"Enrichissement hotels - fin de lot ({nb_traitees} traite(s))")

    return lignes_restantes


if __name__ == "__main__":
    restantes = executer_enrichissement_hotels()
    if restantes:
        raise SystemExit(2)
