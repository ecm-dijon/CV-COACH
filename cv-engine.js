/* cv-engine.js : relecture de CV par règles, 100 % dans le navigateur (aucune donnée envoyée).
   extract()  : lit le PDF avec pdf.js (texte + positions)
   analyze()  : applique les règles du modèle ECM
   annotate() : souligne dans le PDF d'origine (pdf-lib) et ajoute les pages de commentaires */
(function (root) {
"use strict";

const RED = [0.84, 0.14, 0.16], BLUE = [0.12, 0.37, 0.75], INK = [0.09, 0.14, 0.23], GREY = [0.34, 0.39, 0.48];
const LET = "A-Za-zÀ-ÖØ-öø-ÿŒœ";
const NOW_YEAR = new Date().getFullYear();

// Les anciens navigateurs (Safari < 16.4) ne comprennent pas les « lookbehind » : on retombe sur une version simplifiée.
const lb = (src, flags) => { try { return new RegExp(src, flags); } catch (e) { return new RegExp(src.replace(/\(\?<[!=][^)]*\)/g, ""), flags); } };
const strip = s => s.normalize("NFD").replace(/[\u0300-\u036f]/g, "");
const norm = s => strip(String(s)).toLowerCase().replace(/[’‘]/g, "'").replace(/[^a-z0-9' ]+/g, " ").replace(/\s+/g, " ").trim();

/* ------------------------------------------------------------------ */
/* 1. Extraction                                                       */
/* ------------------------------------------------------------------ */
async function extract(pdfjs, bytes) {
  const pdf = await pdfjs.getDocument({ data: bytes.slice(0) }).promise;
  const pages = [];
  for (let n = 1; n <= pdf.numPages; n++) {
    const page = await pdf.getPage(n);
    const [x0, y0, x1, y1] = page.view;
    const content = await page.getTextContent();
    const runs = [];
    for (const it of content.items) {
      if (!("str" in it) || !it.str.trim()) continue;
      const tr = it.transform, len = it.str.length, w = it.width || 0;
      const lead = len - it.str.trimStart().length, trail = len - it.str.trimEnd().length;
      runs.push({
        str: it.str.trim(),
        x: tr[4] + (w * lead) / len,
        y: tr[5],
        w: (w * (len - lead - trail)) / len,
        h: Math.hypot(tr[2], tr[3]) || it.height || 10,
        page: n - 1,
      });
    }
    let hasImage = false;
    try {
      const ops = await page.getOperatorList(), O = pdfjs.OPS;
      hasImage = ops.fnArray.some(f => f === O.paintImageXObject || f === O.paintInlineImageXObject || f === O.paintJpegXObject);
    } catch (e) { /* sans importance */ }
    pages.push({ n: n - 1, x0, y0, w: x1 - x0, h: y1 - y0, rotate: page.rotate || 0, runs, hasImage });
  }
  return buildDoc(pages);
}

/* L'école ajoute en haut des CV un encadré (logo, « ECM Ecole de Commerce et Management », www.ecm-france.fr,
   coordonnées du CREE). Il est normal : on l'écarte de l'analyse et des annotations. */
function dropEcmHeader(page) {
  const anchors = page.runs.filter(r => r.y >= page.y0 + page.h * 0.6 &&
    (/^(https?:\/\/)?(www\.)?ecm-france\.fr/i.test(r.str) || /^ecm\s+[ée]cole de commerce et/i.test(r.str)));
  page.header = [];
  if (!anchors.length) return;
  const cut = Math.min(...anchors.map(a => a.y)) - 2.5 * Math.max(...anchors.map(a => a.h));
  page.header = page.runs.filter(r => r.y >= cut);
  page.runs = page.runs.filter(r => r.y < cut);
}

function splitColumns(page) {
  const W = page.w, runs = page.runs;
  if (runs.length < 12) return null;
  const bins = new Uint8Array(Math.ceil(W) + 2);
  for (const r of runs) {
    const a = Math.max(0, Math.floor(r.x - page.x0)), b = Math.min(bins.length - 1, Math.ceil(r.x - page.x0 + r.w));
    for (let i = a; i <= b; i++) bins[i] = 1;
  }
  const lo = Math.floor(W * 0.22), hi = Math.ceil(W * 0.65);
  let best = { len: 0, mid: 0 }, start = null;
  for (let i = lo; i <= hi; i++) {
    if (!bins[i]) { if (start === null) start = i; }
    else if (start !== null) { if (i - start > best.len) best = { len: i - start, mid: (start + i) / 2 }; start = null; }
  }
  if (start !== null && hi - start + 1 > best.len) best = { len: hi - start + 1, mid: (start + hi) / 2 };
  if (best.len < 0.02 * W) return null;
  const mid = page.x0 + best.mid;
  const left = runs.filter(r => r.x + r.w / 2 < mid), right = runs.filter(r => r.x + r.w / 2 >= mid);
  return left.length < 5 || right.length < 5 ? null : { left, right };
}

function toLines(runs, page, col) {
  const rs = runs.slice().sort((a, b) => b.y - a.y || a.x - b.x);
  const clusters = [];
  for (const r of rs) {
    const c = clusters[clusters.length - 1];
    if (c && Math.abs(r.y - c.y) <= Math.max(1.5, 0.35 * c.h)) { c.runs.push(r); c.h = Math.max(c.h, r.h); }
    else clusters.push({ y: r.y, h: r.h, runs: [r] });
  }
  return clusters.map(c => {
    c.runs.sort((a, b) => a.x - b.x);
    let text = ""; const segs = [];
    c.runs.forEach((r, i) => {
      if (i > 0) { const p = c.runs[i - 1]; if (r.x - (p.x + p.w) > 0.2 * c.h) text += " "; }
      segs.push({ s: text.length, e: text.length + r.str.length, x: r.x, w: r.w });
      text += r.str;
    });
    const last = c.runs[c.runs.length - 1];
    return { text, segs, x: c.runs[0].x, w: last.x + last.w - c.runs[0].x, y: c.y, h: c.h, page: page.n, col };
  });
}

const SECTIONS = [
  ["contact", /^(informations?( personnelles?)?|contact|coordonnees)$/],
  ["logiciels", /^(logiciels?|outils( informatiques?)?|informatique|competences informatiques)$/],
  ["competences", /^(competences?( cles?)?|savoir faire|atouts)$/],
  ["langues", /^langues?$/],
  ["interets", /^(centres? d'interets?|loisirs?|interets?|hobbies|activites extra professionnelles?)$/],
  ["experiences", /^(experiences?( professionnelles?)?|parcours professionnel|experiences? en entreprise)$/],
  ["formations", /^(formations?|etudes|parcours scolaire|parcours academique|diplomes?)$/],
];
function headingKey(text) {
  if (text.length > 45) return null;
  const n = norm(text);
  for (const [k, re] of SECTIONS) if (re.test(n)) return k;
  return null;
}

function buildDoc(pages) {
  const lines = [];
  for (const p of pages) {
    dropEcmHeader(p);
    const sp = splitColumns(p);
    if (sp) lines.push(...toLines(sp.left, p, "L"), ...toLines(sp.right, p, "R"));
    else lines.push(...toLines(p.runs, p, "M"));
  }
  const sections = {}, preamble = [];
  let cur = null, lastCol = null;
  lines.forEach((ln, i) => {
    ln.i = i;
    if (ln.col !== lastCol) { cur = null; lastCol = ln.col; }
    const key = headingKey(ln.text);
    if (key) { cur = sections[key] || (sections[key] = { key, head: ln, lines: [] }); return; }
    (cur ? cur.lines : preamble).push(ln);
  });
  return { pages, lines, sections, preamble };
}

function rectFor(line, from, to) {
  let x1 = null, x2 = null;
  for (const s of line.segs) {
    const a = Math.max(from, s.s), b = Math.min(to, s.e);
    if (b <= a) continue;
    const len = s.e - s.s, sx = s.x + (s.w * (a - s.s)) / len, ex = s.x + (s.w * (b - s.s)) / len;
    if (x1 === null || sx < x1) x1 = sx;
    if (x2 === null || ex > x2) x2 = ex;
  }
  if (x1 === null) { x1 = line.x; x2 = line.x + line.w; }
  return { page: line.page, x: x1, y: line.y, w: Math.max(x2 - x1, 4), h: line.h, end: line.x + line.w };
}

/* ------------------------------------------------------------------ */
/* 2. Données de référence                                             */
/* ------------------------------------------------------------------ */
const OFFICIAL = [
  "Parcours Global ECM Business", "Parcours Global ECM Communication", "Parcours Global ECM Management",
  "Parcours Global ECM Ressources Humaines", "Parcours Global ECM Finance", "Parcours Global ECM International",
  "BTS NDRC (Négociation et Digitalisation de la Relation Client)", "BTS GPME (Gestion de la PME)", "BTS Tourisme",
  "Bachelor 3 Responsable d’Activité Commerciale et Marketing",
  "Bachelor 3 Responsable Projet Communication",
  "Bachelor 3 Chargé des Ressources Humaines",
  "Bachelor 3 Responsable en Gestion d’activité, option Piloter une activité de Gestion Financière",
  "Bachelor 3 Responsable en Gestion d’activité, option Piloter le développement d’un centre de profit",
  "Licence 3 Commerce Vente Marketing (Cnam)",
  "Mastère Professionnel Manager Marketing et de la Relation Client",
  "Mastère Professionnel Manager Ressources Humaines",
  "Mastère Professionnel Expert Financier",
  "Mastère Professionnel Management Stratégique des Organisations",
  "Mastère Professionnel Manager de la Communication Omnicanale",
  "Master Marketing-Vente (Cnam), parcours Marketing dans un monde digital",
];
const STOP = new Set(["de", "des", "du", "la", "le", "les", "et", "en", "d", "l", "a", "au", "aux", "un", "une", "option", "parcours", "ecm", "professionnel"]);
const tokens = s => norm(s).replace(/'/g, " ").split(" ").filter(t => t && !STOP.has(t));
const TYPE_TOKENS = /\b(licence|bachelor|master|mastere|bts|titre|global)\b/;

const SPELL = {
  aout: "août", fevrier: "février", decembre: "décembre", developement: "développement", dévelopement: "développement",
  competence: "compétence", competences: "compétences", experience: "expérience", experiences: "expériences",
  responsabilite: "responsabilité", responsabilites: "responsabilités", reseau: "réseau", reseaux: "réseaux",
  interet: "intérêt", interets: "intérêts", apres: "après", telephone: "téléphone", mobilite: "mobilité",
  creer: "créer", gerer: "gérer", etude: "étude", etudes: "études", etudiant: "étudiant", etudiante: "étudiante",
  resultat: "résultat", resultats: "résultats", qualite: "qualité", clientele: "clientèle", strategie: "stratégie",
  strategique: "stratégique", deja: "déjà", tres: "très", aupres: "auprès", specialite: "spécialité",
  specialites: "spécialités", diplome: "diplôme", mastere: "mastère", evenement: "événement", evenements: "événements",
  redaction: "rédaction", negociation: "négociation", efficacite: "efficacité", creation: "création",
  francais: "français", baccalaureat: "baccalauréat", scolarite: "scolarité", periode: "période",
  evolution: "évolution", elaboration: "élaboration", evaluation: "évaluation", integration: "intégration",
  realiser: "réaliser", realisation: "réalisation", elaborer: "élaborer", reponse: "réponse", reponses: "réponses",
  presence: "présence", polyvalence: null,
};

/* ------------------------------------------------------------------ */
/* 3. Règles                                                           */
/* ------------------------------------------------------------------ */
function analyze(doc) {
  const F = [], POS = [], L = doc.lines, S = doc.sections;
  const fullText = L.map(l => l.text).join("\n");
  const english = (fullText.match(/\b(experience|education|skills|languages|summary|projects|volunteer|references|internship)\b/gi) || []).length >= 3;

  const hits = (re, lines = L) => {
    const out = [], g = new RegExp(re.source, re.flags.includes("g") ? re.flags : re.flags + "g");
    for (const line of lines) { g.lastIndex = 0; let m; while ((m = g.exec(line.text))) { out.push({ line, from: m.index, to: m.index + m[0].length, m }); if (!m[0].length) g.lastIndex++; } }
    return out;
  };
  const whole = line => ({ line, from: 0, to: line.text.length });
  const add = (kind, id, title, comment, targets) => {
    const t = (targets || []).filter(Boolean);
    const q = t[0] ? t[0].line.text : "";
    F.push({ kind, id, title, comment, targets: t, quote: q.length > 90 ? q.slice(0, 88) + "…" : q });
  };
  const ok = s => POS.push(s);

  /* --- Longueur, photo --- */
  if (doc.pages.length > 1) add("advice", "pages", "Plus d’une page", "Un CV d’étudiant tient sur une page. Garde l’essentiel et supprime ce qui n’aide pas à décrocher un entretien.", []);
  else ok("CV sur une page");
  if (doc.pages[0] && doc.pages[0].hasImage) ok("Photo présente");
  else add("advice", "photo", "Pas de photo détectée", "La photo est facultative, mais elle figure dans le modèle de l’école : un portrait net, fond neutre, humanise ta candidature.", []);

  /* --- Contact --- */
  const emails = hits(/[\w.+-]+@[\w-]+(?:\.[\w-]+)+/i);
  if (!emails.length) add("error", "email", "Adresse e-mail introuvable", "Un recruteur doit pouvoir te répondre en un clic : ajoute une adresse e-mail professionnelle (prenom.nom@…).", []);
  else {
    const fake = emails.filter(h => /(reallygreatsite|example\.|@email\.|@domain\.|@test\.|votre|monsite|yourmail|nom\.prenom|prenom\.nom@)/i.test(h.m[0]));
    const silly = emails.filter(h => !fake.includes(h) && /(sexy|cute|baby|princess|swag|gamer|lol|mdr|love)/i.test(h.m[0].split("@")[0]));
    if (fake.length) add("error", "email-demo", "E-mail d’exemple", "Cette adresse vient du modèle de départ : remplace-la par ta vraie adresse, sinon aucun recruteur ne pourra te répondre.", fake);
    else if (silly.length) add("advice", "email-pro", "E-mail peu professionnel", "Crée une adresse sobre de type prenom.nom@gmail.com pour tes candidatures.", silly);
    else ok("E-mail présent");
  }
  const phones = hits(/(?:\+33\s?|0033\s?|0)[1-9](?:[\s.\-]?\d{2}){4}/);
  if (!phones.length) add("error", "tel", "Téléphone introuvable", "Ajoute un numéro de téléphone : c’est souvent le premier moyen de contact d’un recruteur.", []);
  else {
    const demo = phones.filter(h => /(?:0[1-9][\s.]?12[\s.]?34[\s.]?56[\s.]?78|01[\s.]?23[\s.]?45[\s.]?67[\s.]?89)/.test(h.m[0]));
    const compact = phones.filter(h => /^\d{10}$/.test(h.m[0]));
    if (demo.length) add("error", "tel-demo", "Numéro d’exemple", "Ce numéro est un faux numéro de modèle : remplace-le par le tien.", demo);
    else if (compact.length) add("advice", "tel-format", "Numéro à espacer", "Écris ton numéro par paires pour qu’il se lise d’un coup d’œil : 06 12 34 56 78.", compact);
    else ok("Téléphone présent");
  }
  if (!/linkedin/i.test(fullText)) add("advice", "linkedin", "Pas de lien LinkedIn", "Ajoute l’adresse de ton profil LinkedIn : les recruteurs le consultent presque toujours.", []);
  const street = hits(/\b\d{1,3}\s?(?:bis|ter)?,?\s+(?:rue|avenue|av\.|boulevard|bd|chemin|impasse|all[ée]e|place|route|quai|cours|square|r[ée]sidence)\b[^\n]*/i);
  if (street.length) add("advice", "adresse", "Adresse complète inutile", "La ville suffit : inutile de donner ton adresse postale complète sur un CV (et c’est plus prudent).", street);
  const perso = hits(/(situation familiale|c[ée]libataire|pacs[ée]e?|divorc[ée]e?|mari[ée]e?\b|nombre d['’]enfants|n[°o]\s?s[ée]cu|s[ée]curit[ée] sociale|nationalit[ée])/i);
  if (perso.length) add("error", "perso", "Information à supprimer", "La situation familiale, la nationalité et le numéro de sécurité sociale n’ont rien à faire sur un CV : retire-les.", perso);
  const birth = hits(/n[ée]e?\s+le\s+\d{1,2}[\/.]\d{1,2}[\/.]\d{2,4}|\b\d{1,2}[\/.]\d{1,2}[\/.](?:19|20)\d{2}\b/i);
  if (birth.length) add("advice", "naissance", "Date de naissance", "Remplace la date de naissance par ton âge (« 19 ans »), comme dans le modèle de l’école.", birth);
  const placeholders = hits(/(lorem ipsum|votre nom|nom pr[ée]nom|\[.*?\]|xxxx+)/i);
  if (placeholders.length) add("error", "placeholder", "Texte d’exemple oublié", "Ce passage vient du modèle de départ : remplace-le ou supprime-le.", placeholders);

  /* --- Sections du modèle --- */
  const wanted = [["contact", "INFORMATIONS"], ["logiciels", "LOGICIELS"], ["competences", "COMPÉTENCES"], ["langues", "LANGUES"], ["interets", "CENTRES D’INTÉRÊT"], ["experiences", "EXPÉRIENCES PROFESSIONNELLES"], ["formations", "FORMATIONS"]];
  const missing = wanted.filter(([k]) => !S[k]).map(([, n]) => n);
  if (missing.length) add("advice", "sections", "Rubriques absentes", "Par rapport au modèle de l’école, il manque : " + missing.join(", ") + ". Ajoute-les, même courtes.", []);
  else ok("Toutes les rubriques du modèle sont présentes");
  if (S.experiences && S.formations && S.formations.head.i < S.experiences.head.i && S.formations.head.col === S.experiences.head.col)
    add("advice", "ordre", "Ordre des rubriques", "Dans le modèle, les expériences passent avant les formations : en alternance, c’est ce qui prouve que tu sais travailler.", [whole(S.formations.head)]);

  /* --- Ligne de recherche, titre, profil --- */
  const pre = doc.preamble;
  const iSearch = pre.findIndex(l => /recherche/i.test(l.text) && /alternance|stage|apprentissage|emploi/i.test(l.text));
  let used = new Set();
  if (iSearch < 0) {
    add("error", "recherche", "Ligne de recherche absente", "Ajoute sous ton nom une ligne qui dit ce que tu cherches. Modèle : « À la recherche d’une alternance de 24 mois, à partir de septembre 2026, dans le cadre de ma licence … ».", []);
  } else {
    const grp = [pre[iSearch]];
    for (let k = iSearch + 1; k < Math.min(pre.length, iSearch + 3); k++) {
      const t = pre[k].text, up = t.replace(/[^A-Za-zÀ-ÿ]/g, "");
      if (up && up === up.toUpperCase() && up.length > 5) break;
      if (grp.map(g => g.text).join(" ").length + t.length > 230) break;
      grp.push(pre[k]);
    }
    grp.forEach(g => used.add(g));
    const txt = grp.map(g => g.text).join(" ");
    const gaps = [];
    if (!/alternance|apprentissage|professionnalisation|stage/i.test(txt)) gaps.push("le type de contrat");
    if (!/\b\d{1,2}\s*(mois|ans?|semaines?)\b|\bun an\b|\bdeux ans\b/i.test(txt)) gaps.push("la durée");
    if (!/(janvier|f[ée]vrier|mars|avril|mai|juin|juillet|ao[uû]t|septembre|octobre|novembre|d[ée]cembre|rentr[ée]e)/i.test(txt)) gaps.push("la date de début");
    if (!/(licence|bachelor|mast[èe]re?|master|bts|parcours global|dipl[ôo]me|titre|formation)/i.test(txt)) gaps.push("la formation préparée");
    if (gaps.length) add("error", "recherche", "Ligne de recherche incomplète", "Il manque " + gaps.join(", ") + ". Modèle : « À la recherche d’une alternance de 24 mois, à partir de septembre 2026, dans le cadre de ma licence … ».", [whole(grp[0])]);
    else ok("Ligne de recherche complète (contrat, durée, début, formation)");
    const next = pre[iSearch + grp.length];
    if (next) {
      const up = next.text.replace(/[^A-Za-zÀ-ÿ]/g, "");
      if (up.length > 5 && up === up.toUpperCase() && next.text.length < 60) {
        used.add(next);
        if (/\s[-–—]\s/.test(next.text)) add("advice", "titre", "Titre trop précis", "Garde un titre de métier large, sans nom d’entreprise : il te permet de candidater à plusieurs postes (par exemple « ASSISTANT COMMERCIAL »).", [whole(next)]);
        else ok("Titre de métier présent");
      }
    }
    const prof = pre.filter(l => !used.has(l) && l.text.length >= 35 && l.page === pre[iSearch].page && l.col === pre[iSearch].col && l.i > pre[iSearch].i);
    const words = prof.reduce((n, l) => n + l.text.split(/\s+/).length, 0);
    if (!prof.length) add("advice", "profil", "Pas de profil", "Ajoute un court profil de 3 à 4 lignes : tes qualités concrètes, puis ce que tu veux apporter à l’équipe.", []);
    else if (words > 75 || prof.length > 6) add("advice", "profil", "Profil trop long", "Ton profil doit tenir en 3 ou 4 lignes : garde deux qualités concrètes et ce que tu veux apporter.", [whole(prof[0])]);
    else if (words < 20) add("advice", "profil", "Profil trop court", "Développe un peu : deux qualités concrètes et ce que tu veux apporter à l’équipe.", [whole(prof[0])]);
    else ok("Profil de longueur correcte");
    const fem = hits(/(charg[ée]e|assistante|[ée]tudiante|alternante|conseill[èe]re|vendeuse|animatrice|apprentie)/i, L.filter(l => !(S.formations && S.formations.lines.includes(l))));
    const masc = hits(lb("(?<![A-Za-zÀ-ÿ])(motiv[ée]|habitu[ée]|passionn[ée]|organis[ée]|impliqu[ée]|investi|curieux|rigoureux|s[ée]rieux)(?![A-Za-zÀ-ÿ])", "i"), prof);
    if (fem.length && masc.length) add("error", "accord", "Accord au masculin", "Ton CV parle de toi au féminin (« " + fem[0].m[0] + " ») mais ton profil est accordé au masculin : harmonise (« Motivée », « Habituée »…).", masc);
  }

  /* --- Formations --- */
  const forms = S.formations ? S.formations.lines : [];
  const ecmName = hits(/[ée]cole de commerce et de management/i);
  if (ecmName.length) add("error", "ecm", "Nom de l’école", "Le nom officiel s’écrit « École de Commerce et Management », sans « de » avant Management.", ecmName);
  let officialOk = false, officialSeen = false;
  const mentionsEcm = /\becm\b|ecole de commerce et (de )?management/.test(norm(fullText));
  const bad = [];
  for (const ln of forms) {
    const n = norm(ln.text);
    if (!TYPE_TOKENS.test(n)) continue;
    const A = new Set(tokens(ln.text));
    let best = { score: 0, title: "" };
    for (const t of OFFICIAL) {
      const B = tokens(t); const hit = B.filter(x => A.has(x)).length;
      const score = hit / B.length;
      if (score > best.score) best = { score, title: t };
    }
    if (best.score >= 0.5) {
      officialSeen = true;
      if (n.includes(norm(best.title)) || norm(best.title).includes(n)) officialOk = true;
      else bad.push({ ln, title: best.title });
    }
  }
  if (bad.length) bad.forEach(b => add("error", "formation", "Intitulé de formation", "L’intitulé officiel est : « " + b.title + " ». Recopie-le mot pour mot : un recruteur vérifie parfois, et l’école aussi.", [whole(b.ln)]));
  else if (officialOk) ok("Intitulé de formation conforme à la liste officielle");
  else if (S.formations && mentionsEcm && !officialSeen) add("advice", "formation-inconnue", "Intitulé non reconnu", "Je ne retrouve pas ta formation dans la liste officielle de l’ECM Dijon. Vérifie son intitulé exact auprès de ton CREE.", [whole(S.formations.head)]);

  const ranges = hits(/((?:19|20)\d{2})\s*[-–—]\s*((?:19|20)\d{2})/);
  const inverted = ranges.filter(h => +h.m[2] < +h.m[1]);
  if (inverted.length) add("error", "dates-inversees", "Dates inversées", "L’année de fin est antérieure à celle de début : vérifie tes dates.", inverted);
  const age = (fullText.match(lb("(?<!\\d)(1[6-9]|[2-3]\\d)\\s*ans\\b", "")) || [])[1];
  if (age) {
    const birthYear = NOW_YEAR - +age;
    const odd = ranges.filter(h => !inverted.includes(h) && +h.m[1] < birthYear + 13);
    if (odd.length) add("error", "dates-age", "Dates incohérentes avec ton âge", "Avec " + age + " ans, ces années ne collent pas : vérifie tes dates d’études ou ton âge.", odd);
  }
  const empty = hits(/^\s*(sp[ée]cialit[ée]s?|options?|mentions?|sp[ée]cialisations?)\s*:?\s*$/i);
  if (empty.length) add("error", "vide", "Rubrique vide", "Complète cette ligne (tes spécialités ou options) ou supprime-la : une ligne vide fait négligé.", empty);

  /* --- Expériences --- */
  const exp = S.experiences ? S.experiences.lines : [];
  const DATE_LINE = /(?:\d{4}.*(?:\d{4}|aujourd|pr[ée]sent|actuel|ce jour)|(?:janv|f[ée]vr|mars|avr|mai|juin|juil|ao[uû]t|sept|oct|nov|d[ée]c)[a-zéû.]*\s*\d{4})/i;
  const dateIdx = exp.map((l, i) => (DATE_LINE.test(l.text) ? i : -1)).filter(i => i >= 0);
  const entries = dateIdx.map((di, k) => ({
    title: exp[di - 1] || exp[di], date: exp[di],
    bullets: exp.slice(di + 1, k + 1 < dateIdx.length ? dateIdx[k + 1] - 1 : exp.length),
  }));
  const allBullets = entries.flatMap(e => e.bullets);
  const INF_NOT = new Set(["dossier", "atelier", "premier", "dernier", "cahier", "courrier", "papier", "panier", "quartier", "employer"]);
  const INF_IRRE = /^(mettre|prendre|suivre|vendre|conduire|construire|produire|réduire|fournir|établir|définir|choisir|réussir|obtenir|maintenir|offrir|ouvrir|accueillir|atteindre|apprendre|comprendre|permettre|recevoir|faire|écrire)$/i;
  const firstWord = b => (b.text.replace(/^[•\-–·●▪◦\s]+/, "").match(new RegExp("^[" + LET + "’']+")) || [""])[0];
  const cat = b => { const w = firstWord(b).toLowerCase(); if (!w) return null; return (w.length >= 4 && /er$/.test(w) && !INF_NOT.has(w)) || INF_IRRE.test(w) ? "inf" : "nom"; };
  entries.forEach(e => {
    if (e.bullets.length && e.bullets.length < 3) add("advice", "missions", "Missions trop courtes", "Détaille cette expérience : 4 à 6 missions concrètes montrent ce que tu sais faire.", [e.title && whole(e.title)]);
    else if (e.bullets.length > 8) add("advice", "missions-long", "Trop de missions", "Garde les 6 ou 7 missions les plus parlantes pour le poste visé.", [e.title && whole(e.title)]);
    if (e.bullets.length >= 3 && !e.bullets.some(b => /\d/.test(b.text))) add("advice", "chiffres", "Aucun chiffre", "Ajoute au moins un chiffre ou un volume (nombre de clients, d’événements, d’appels, de campus…) : c’est ce qui rend une mission crédible.", [e.title && whole(e.title)]);
  });
  const weak = hits(/^[•\-–·●▪◦\s]*(aider|participer|assister|contribuer|soutenir)(?![A-Za-zÀ-ÿ])/i, allBullets);
  if (weak.length) add("advice", "verbes-faibles", "Verbes trop faibles", "« Aider à », « participer à » minimisent ton rôle. Dis ce que tu as fait : créer, piloter, analyser, organiser…", weak);
  const kinds = allBullets.map(cat);
  const nInf = kinds.filter(k => k === "inf").length, nNom = kinds.filter(k => k === "nom").length;
  if (nInf >= 2 && nNom >= 2) {
    const minority = nNom <= nInf ? "nom" : "inf";
    const tg = allBullets.filter((b, i) => kinds[i] === minority).map(b => { const w = firstWord(b), from = b.text.indexOf(w); return { line: b, from, to: from + w.length }; });
    add("advice", "puces", "Puces non homogènes", "Une expérience commence ses missions par des verbes à l’infinitif (« Assurer… »), l’autre par des noms (« Gestion… »). Choisis une seule forme pour tout le CV.", tg);
  }
  const trailing = hits(/[,;]\s*$/, allBullets);
  if (trailing.length) add("error", "virgule-fin", "Virgule en fin de mission", "On ne termine pas une puce par une virgule : retire-la (ou mets un point partout, mais sois cohérent).", trailing);
  const starts = entries.map(e => { const m = e.date.text.match(/((?:19|20)\d{2})/); return m ? +m[1] : null; });
  entries.forEach((e, i) => { if (i && starts[i] && starts[i - 1] && starts[i] > starts[i - 1]) add("advice", "chrono", "Ordre chronologique", "Place l’expérience la plus récente en premier : c’est elle que le recruteur lit d’abord.", [whole(e.date)]); });
  if (entries.length && !weak.length && !trailing.length && entries.every(e => e.bullets.length >= 4)) ok("Expériences détaillées");

  /* --- Logiciels, compétences, langues, centres d’intérêt --- */
  const gen = hits(/^(outils? bureautiques?|pack office|(?:microsoft )?office|suite office|informatique)\b/i, S.logiciels ? S.logiciels.lines : []);
  if (gen.length) add("advice", "outils", "Outils trop vagues", "Nomme tes outils (Word, Excel, PowerPoint) et ton niveau : « bureautique » ne dit rien à un recruteur.", gen);
  const crm = hits(/^CRM$/i, S.logiciels ? S.logiciels.lines : []);
  if (crm.length) add("advice", "crm", "CRM à préciser", "Dis quel CRM tu as utilisé (Zoho, Salesforce, HubSpot…) : c’est un mot-clé que cherchent les recruteurs.", crm);
  if (S.competences && S.competences.lines.length > 5) add("advice", "competences", "Trop de compétences", "Garde 4 compétences métier au maximum, celles qui comptent vraiment pour le poste.", [whole(S.competences.head)]);
  if (S.langues) {
    const noLevel = S.langues.lines.filter(l => /(anglais|espagnol|allemand|italien|portugais|arabe|chinois|mandarin|russe|n[ée]erlandais|japonais|turc|polonais|fran[çc]ais)/i.test(l.text) && !/\b[ABC][12]\b/i.test(l.text));
    if (noLevel.length) add("advice", "niveau-langue", "Niveau de langue", "Indique ton niveau avec l’échelle européenne (A1 à C2) : « courant » ou « bon niveau » ne se vérifient pas.", noLevel.map(whole));
    else if (S.langues.lines.length) ok("Langues avec niveau");
  }
  const vague = new Set(["sport", "sports", "lecture", "voyage", "voyages", "cinema", "musique", "cuisine", "jeux video", "series", "shopping", "sorties", "amis"]);
  const vagueI = (S.interets ? S.interets.lines : []).filter(l => vague.has(norm(l.text)));
  if (vagueI.length) add("advice", "interets", "Centres d’intérêt trop vagues", "Précise : un sport pratiqué depuis combien de temps, dans quel club, quel type de lecture… Un détail suffit à créer une accroche d’entretien.", vagueI.map(whole));

  /* --- Typographie et orthographe --- */
  const typo = (id, title, comment, re, kind) => { const h = hits(re); if (h.length) add(kind || "advice", id, title, comment, h); };
  typo("espace-annee", "Espace manquant", "Il manque une espace entre le mois et l’année.", /(janvier|f[ée]vrier|mars|avril|mai|juin|juillet|ao[uû]t|septembre|octobre|novembre|d[ée]cembre)(?:19|20)\d{2}/i, "error");
  typo("sigle-s", "Pluriel d’un sigle", "En français, un sigle ne prend pas de « ’s » : écris « KPI ».", lb("(?<![A-Za-z])[A-Z]{2,}[’']s(?![A-Za-z])", ""), "error");
  typo("ville-minuscule", "Majuscule à la ville", "Un nom de ville prend une majuscule.", lb("(?<![A-Za-zÀ-ÿ])(dijon|besan[çc]on|belfort|paris|lyon|marseille|strasbourg|mulhouse|nancy|chalon|beaune|lille|nantes|bordeaux|toulouse)(?![A-Za-zÀ-ÿ])", ""), "error");
  typo("a-laise", "Accent manquant", "On écrit « à l’aise » avec un accent sur le à.", lb("(?<![A-Za-zÀ-ÿ])a l[’']aise", "i"), "error");
  typo("chalon", "Orthographe de la ville", "Vérifie : Chalon-sur-Saône s’écrit sans accent circonflexe (Châlons-en-Champagne est une autre ville).", /Châlon(?![s-])/);
  typo("tiret-dates", "Espaces autour du tiret", "Mets une espace de chaque côté du tiret dans les dates : « Février 2024 - Août 2025 ».", /\d{4}-\s|\s-(?=\d{4})/);
  typo("deux-points", "Espace avant les deux-points", "En français, on met une espace avant les deux-points : « Mobilité : Dijon ».", new RegExp("[" + LET + "]:(?=\\s|$)"));
  typo("parentheses", "Espace dans la parenthèse", "Pas d’espace après la parenthèse ouvrante ni avant la fermante : « (Roman, BD) ».", /\(\s+|\s+\)/);
  typo("virgule-barre", "Virgule en trop", "Retire la virgule avant la barre verticale.", /,\s*\|/);
  typo("slash", "Espaces autour de la barre oblique", "Mets une espace de chaque côté, ou aucune : « salons / portes ouvertes ».", new RegExp("[" + LET + "]/\\s+[" + LET + "]"));
  typo("double-point", "Deux points de suspension", "Deux points ne se font pas : supprime-les ou écris « … » (et évite les suspensions dans un CV).", lb("(?<!\\.)\\.\\.(?!\\.)", ""));
  typo("repetition", "Mot répété", "Ce mot est écrit deux fois de suite.", lb("(?<![" + LET + "])([" + LET + "]{3,})\\s+\\1(?![" + LET + "])", "i"));
  if (!english) {
    const sp = [];
    for (const ln of L) {
      const re = new RegExp("[" + LET + "’']+", "g"); let m;
      while ((m = re.exec(ln.text))) { const k = m[0].toLowerCase(); if (SPELL[k]) sp.push({ line: ln, from: m.index, to: m.index + m[0].length, w: m[0], fix: SPELL[k] }); }
    }
    if (sp.length) {
      const ex = sp.slice(0, 3).map(s => "« " + s.w + " » → « " + (s.w[0] === s.w[0].toUpperCase() ? s.fix[0].toUpperCase() + s.fix.slice(1) : s.fix) + " »").join(", ");
      add("error", "orthographe", "Accents manquants", "Accents oubliés : " + ex + (sp.length > 3 ? "…" : "") + ". Relis chaque mot, une faute d’orthographe suffit à écarter un CV.", sp);
    }
  }

  /* --- Numérotation dans l’ordre de lecture de la copie --- */
  const pos = f => f.targets.length ? f.targets.reduce((m, t) => Math.min(m, t.line.page * 10000 + (5000 - t.line.y)), Infinity) : Infinity;
  F.sort((a, b) => pos(a) - pos(b));
  F.forEach((f, i) => { f.n = i + 1; f.rects = f.targets.map(t => rectFor(t.line, t.from, t.to)); });
  return { findings: F, positives: POS, errors: F.filter(f => f.kind === "error").length, advice: F.filter(f => f.kind === "advice").length };
}

/* ------------------------------------------------------------------ */
/* 4. Annotation du PDF                                                */
/* ------------------------------------------------------------------ */
const clean = s => String(s).replace(/[\r\n\t\u00A0\u202F]+/g, " ").replace(/→/g, "->").replace(/[^\x20-\x7E\u00A1-\u00FF\u0152\u0153\u2013\u2014\u2018\u2019\u201C\u201D\u2022\u2026\u20AC]/g, "?");

async function annotate(PDFLib, bytes, doc, result, opts = {}) {
  const { PDFDocument, StandardFonts, rgb } = PDFLib;
  const pdf = await PDFDocument.load(bytes, { ignoreEncryption: true });
  const font = await pdf.embedFont(StandardFonts.Helvetica), bold = await pdf.embedFont(StandardFonts.HelveticaBold), ital = await pdf.embedFont(StandardFonts.HelveticaOblique);
  const pages = pdf.getPages();
  const col = k => (k === "error" ? rgb(...RED) : rgb(...BLUE));
  const placed = {};

  for (const f of result.findings) {
    for (const t of f.rects) {
      const pg = pages[t.page];
      if (!pg || doc.pages[t.page].rotate) continue;
      const c = col(f.kind);
      pg.drawLine({ start: { x: t.x, y: t.y - 1.8 }, end: { x: t.x + t.w, y: t.y - 1.8 }, thickness: 1.4, color: c, dashArray: f.kind === "error" ? undefined : [2.5, 1.5] });
      const size = pg.getSize(), r = 6.3, list = (placed[t.page] = placed[t.page] || []);
      const bx = Math.max(t.x + t.w, t.end), x0 = Math.min(bx + r + 3, size.width - r - 2);
      let cx = x0, cy = t.y + t.h * 0.32;
      for (let guard = 0; guard < 12 && list.some(p => Math.hypot(p.x - cx, p.y - cy) < 2 * r + 1); guard++) { cx += 2 * r + 1; if (cx > size.width - r - 2) { cx = x0; cy += 2 * r + 1; } }
      list.push({ x: cx, y: cy });
      pg.drawCircle({ x: cx, y: cy, size: r, color: c, borderColor: rgb(1, 1, 1), borderWidth: 0.8 });
      const label = String(f.n), tw = bold.widthOfTextAtSize(label, 7.2);
      pg.drawText(label, { x: cx - tw / 2, y: cy - 2.5, size: 7.2, font: bold, color: rgb(1, 1, 1) });
    }
  }
  if (pages[0]) {
    const stamp = clean("Relecture ECM : " + result.errors + " correction" + (result.errors > 1 ? "s" : "") + ", " + result.advice + " conseil" + (result.advice > 1 ? "s" : "") + " - voir les pages de commentaires");
    const w = bold.widthOfTextAtSize(stamp, 6.5);
    pages[0].drawRectangle({ x: 6, y: 2, width: w + 10, height: 11, color: rgb(1, 1, 1), opacity: 0.92 });
    pages[0].drawText(stamp, { x: 11, y: 5, size: 6.5, font: bold, color: rgb(...RED) });
  }

  /* pages de commentaires */
  const PW = 595.28, PH = 841.89, LM = 76, RM = 50, TW = PW - LM - RM;
  const logo = opts.logoBytes ? await pdf.embedPng(opts.logoBytes) : null;
  let page, y;
  const newPage = first => {
    page = pdf.addPage([PW, PH]);
    page.drawLine({ start: { x: 58, y: 0 }, end: { x: 58, y: PH }, thickness: 1.1, color: rgb(0.84, 0.14, 0.16), opacity: 0.45 });
    y = PH - 56;
    if (first && logo) { const lw = 74, lh = (logo.height / logo.width) * lw; page.drawImage(logo, { x: PW - RM - lw, y: PH - 30 - lh, width: lw, height: lh }); }
  };
  const wrap = (text, f, size, maxW) => {
    const words = clean(text).split(/\s+/).filter(Boolean), out = []; let cur = "";
    for (const w of words) { const t = cur ? cur + " " + w : w; if (f.widthOfTextAtSize(t, size) > maxW && cur) { out.push(cur); cur = w; } else cur = t; }
    if (cur) out.push(cur); return out;
  };
  const need = h => { if (y - h < 56) newPage(false); };
  const para = (text, f, size, color, indent = 0, gap = 3.5) => { for (const ln of wrap(text, f, size, TW - indent)) { need(size + gap); page.drawText(ln, { x: LM + indent, y, size, font: f, color }); y -= size + gap; } };

  newPage(true);
  page.drawText("Copie corrigée", { x: LM, y, size: 24, font: bold, color: rgb(...INK) }); y -= 22;
  page.drawText(clean("Relecture de ton CV - " + new Date().toLocaleDateString("fr-FR")), { x: LM, y, size: 10, font, color: rgb(...GREY) }); y -= 22;
  if (logo) y = Math.min(y, PH - 122);
  para(result.errors + " correction" + (result.errors > 1 ? "s" : "") + " (soulignées en rouge) et " + result.advice + " conseil" + (result.advice > 1 ? "s" : "") + " (soulignés en bleu pointillé). Chaque numéro renvoie au même numéro sur ton CV.", font, 11, rgb(...INK), 0, 4);
  y -= 8;

  for (const f of result.findings) {
    const body = wrap(f.comment, font, 10.5, TW - 28), quote = f.quote ? wrap("Dans ton CV : « " + f.quote + " »", ital, 9, TW - 28) : [];
    need(24 + body.length * 14 + quote.length * 12 + 10);
    const c = col(f.kind);
    page.drawCircle({ x: LM + 8, y: y - 3, size: 8.5, color: c });
    const lab = String(f.n), lw = bold.widthOfTextAtSize(lab, 9);
    page.drawText(lab, { x: LM + 8 - lw / 2, y: y - 6.2, size: 9, font: bold, color: rgb(1, 1, 1) });
    page.drawText(clean(f.title), { x: LM + 26, y: y - 6, size: 11.5, font: bold, color: rgb(...INK) });
    const tag = f.kind === "error" ? "À CORRIGER" : "CONSEIL", tgw = bold.widthOfTextAtSize(tag, 7.5);
    page.drawText(tag, { x: PW - RM - tgw, y: y - 5.5, size: 7.5, font: bold, color: c });
    y -= 22;
    for (const ln of body) { page.drawText(ln, { x: LM + 26, y, size: 10.5, font, color: rgb(...INK) }); y -= 14; }
    for (const ln of quote) { page.drawText(ln, { x: LM + 26, y, size: 9, font: ital, color: rgb(...GREY) }); y -= 12; }
    y -= 10;
  }
  if (!result.findings.length) para("Aucun point à corriger n’a été détecté par la relecture automatique. Fais tout de même relire ton CV par ton CREE.", font, 11, rgb(...INK));

  if (result.positives.length) {
    need(60); y -= 6;
    page.drawText("Ce qui est conforme au modèle", { x: LM, y, size: 13, font: bold, color: rgb(...INK) }); y -= 20;
    for (const p of result.positives) para("•  " + p, font, 10.5, rgb(...INK), 0, 4);
    y -= 6;
  }
  need(90); y -= 10;
  para("Cette relecture est automatique : elle vérifie la forme (rubriques du modèle, dates, intitulé de formation officiel, orthographe courante, typographie) mais ne juge ni la qualité de tes formulations ni la mise en page. Fais valider ton CV par ton CREE avant de l’envoyer. Ton CV n’a pas quitté ton ordinateur.", ital, 9, rgb(...GREY), 0, 3.5);
  return pdf.save();
}

root.CVEngine = { extract, analyze, annotate, OFFICIAL };
})(typeof window !== "undefined" ? window : globalThis);
