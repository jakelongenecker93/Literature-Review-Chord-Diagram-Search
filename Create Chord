import argparse
import glob
import csv
import html as html_escape
import json
import math
import os
import re
from collections import Counter, defaultdict
from itertools import combinations
from pypdf import PdfReader


# ------------------------------- CATEGORY VOCAB -------------------------------
CATEGORY_KEYWORDS = {
    "Georeferencing & Registration": {
        "georeference", "geolocation", "geolocate",
        "registration", "misregistration",
        "coregistration", "coregister",
        "rectification", "rectify",
        "orthorectification", "orthorectify",
        "reprojection", "reproject",
        "gcp",
        "featurematching",
        "boresight", "attitude", "parallax",
        "resampling", "resample",
        "warp", "transform", "affine",
    },
    "Agriculture": {
        "crop", "cropland", "irrigation",
        "soilmoisture", "evapotranspiration", "et",
        "canopytemperature", "waterstress", "drought",
        "yield", "productivity", "phenology",
        "ndvi", "vegetation"
    },
    "Aquaculture": {
        "aquaculture", "fishery",
        "heatstress", "mortality", "disease",
        "waterquality", "dissolvedoxygen", "hypoxia",
        "salinity", "turbidity", "chlorophyll",
        "algalbloom"
    },
    "Biodiversity & Conservation": {
        "biodiversity", "species", "habitat",
        "conservation", "protectedarea",
        "fragmentation", "connectivity",
        "restoration", "deforestation",
        "resilience", "vulnerability",
        "wetland", "mangrove", "invasive"
    },
    "Coastal & Marine Resources": {
        "sst", "seasurfacetemperature",
        "coral", "reef", "bleach", "bleaching",
        "marineheatwave", "upwelling",
        "seagrass", "kelp",
        "turbidity", "sediment", "chlorophyll"
    },
    "Cryosphere & Water Resources": {
        "glacier", "snow", "albedo",
        "melt", "permafrost",
        "runoff", "streamflow", "hydrology",
        "watershed", "reservoir",
        "flood", "drought",
        "groundwater", "recharge"
    },
    "Geology, Critical Minerals & Volcanoes": {
        "mineral", "criticalmineral", "rareearth",
        "alteration", "hydrothermal",
        "emissivity", "thermalinfrared", "thermalir", "tir",
        "volcano", "eruption", "lava",
        "geothermal", "fault"
    },
    "Urban Resilience": {
        "urban", "uhi", "urbanheatisland",
        "heatwave", "extremeheat",
        "risk", "resilience", "vulnerability",
        "impervioussurface", "greenspace",
        "building", "coolroof", "energy"
    },
    "Wildfires": {
        "wildfire", "burnseverity",
        "fuelmoisture", "activefire",
        "thermalanomaly", "smoke",
        "fireweather", "drought",
        "postfire", "erosion"
    },

    # --- Programming / methods ---
    "Programming Languages": {
        # NOTE: single-letter languages (R, C, etc.) are handled via phrase matching
        # and mapped to these canonical stems so they survive --min-len filtering.
        "rlang", "clang", "python", "matlab", "julia",
        "rmarkdown", "rstudio", "cran",
        "javascript", "typescript", "java",
        "cpp", "csharp",
        "fortran", "scala", "rust", "golang",
        "ruby", "perl", "php",
        "sql",
        "machinecode",
        "plugin",
    },
}

CATEGORY_COLORS = {
    "Georeferencing & Registration": "#e377c2",
    "Agriculture": "#2ca02c",
    "Aquaculture": "#1f77b4",
    "Biodiversity & Conservation": "#17becf",
    "Coastal & Marine Resources": "#9467bd",
    "Cryosphere & Water Resources": "#7f7f7f",
    "Geology, Critical Minerals & Volcanoes": "#8c564b",
    "Urban Resilience": "#ff7f0e",
    "Wildfires": "#d62728",

    # Deep yellow
    "Programming Languages": "#c9a400",
}


# ------------------------------- TOKENIZATION -------------------------------
TOKEN_RE = re.compile(r"[a-zA-Z][a-zA-Z\-]{1,}")
URL_RE = re.compile(r"https?://\S+|www\.\S+")
DOI_RE = re.compile(r"\b10\.\d{4,9}/\S+\b", re.IGNORECASE)
EMAIL_RE = re.compile(r"\b[\w\.-]+@[\w\.-]+\.\w+\b")


# ------------------------------- STEMMER -------------------------------
IES_EXCEPTIONS = {"species", "series", "rabies", "diabetes", "facies"}
IRREGULAR = {
    "indices": "index",
    "matrices": "matrix",
    "analyses": "analysis",
    "theses": "thesis",
    "crises": "crisis",
    "axes": "axis",
}
S_END_EXCEPTIONS = {"glass", "class", "mass", "bias", "analysis", "thesis", "crisis", "axis"}

# Canonicalization overrides (explicit merges)
STEM_OVERRIDES = {
    # resample/resampling/resampled -> resampl
    "resample": "resampl",
    "resampling": "resampl",
    "resampled": "resampl",
    "resamples": "resampl",

    # rectify/rectification (+ common forms) -> rectif
    "rectify": "rectif",
    "rectified": "rectif",
    "rectifying": "rectif",
    "rectifies": "rectif",
    "rectification": "rectif",
    "rectifications": "rectif",

    # geolocate/geolocation -> geolocation
    "geolocate": "geolocation",
    "geolocated": "geolocation",
    "geolocating": "geolocation",
    "geolocates": "geolocation",

    # TIR synonyms -> thermalinfrared (so they COUNT as one node)
    "thermalir": "thermalinfrared",
    "tir": "thermalinfrared",
    "thermal-ir": "thermalinfrared",
    "thermal_ir": "thermalinfrared",
    "t.i.r": "thermalinfrared",
}

def sci_stem(w: str) -> str:
    w = w.lower().strip().replace("-", "")
    if not w:
        return w

    if w in STEM_OVERRIDES:
        return STEM_OVERRIDES[w]

    if w in IRREGULAR:
        return IRREGULAR[w]
    if w in IES_EXCEPTIONS:
        return w

    if w.endswith("'s"):
        w = w[:-2]

    if len(w) > 4 and w.endswith("ies") and w not in IES_EXCEPTIONS:
        w = w[:-3] + "y"
    elif len(w) > 4 and w.endswith("es"):
        if not w.endswith(("ses", "xes", "zes")):
            w = w[:-2]
    elif len(w) > 3 and w.endswith("s"):
        if w not in S_END_EXCEPTIONS and not w.endswith("ss"):
            w = w[:-1]

    if len(w) > 6 and w.endswith("ing"):
        w = w[:-3]
    elif len(w) > 5 and w.endswith("ed"):
        w = w[:-2]
    elif len(w) > 6 and w.endswith("ers"):
        w = w[:-3]
    elif len(w) > 5 and w.endswith("er"):
        w = w[:-2]

    # re-check overrides after stripping suffixes
    if w in STEM_OVERRIDES:
        return STEM_OVERRIDES[w]

    return w


# --------------------- GEOREF: PHRASE MATCHING -> "gcp" ---------------------
GEO_GCP_PHRASE_PATTERNS = [
    re.compile(r"\bgcps?\b", re.IGNORECASE),
    re.compile(r"\bcontrol\s*points?\b", re.IGNORECASE),
    re.compile(r"\bcontrolpoints?\b", re.IGNORECASE),
    re.compile(r"\bground\s*control\s*points?\b", re.IGNORECASE),
    re.compile(r"\bgroundcontrolpoints?\b", re.IGNORECASE),
    re.compile(r"\btie\s*points?\b", re.IGNORECASE),
    re.compile(r"\btiepoints?\b", re.IGNORECASE),
]
BANNED_SINGLE_STEMS = {"point"}  # never count "point" alone


# ---------------- PROGRAMMING LANGUAGES: PHRASE MATCHING ----------------
# Why needed:
# - TOKEN_RE ignores single-letter tokens (e.g., "R", "C").
# - PDF extraction often mangles punctuation (e.g., "C++" -> "c" or "c++").
# Solution:
# - Detect high-signal phrases and map them to canonical stems in CATEGORY_KEYWORDS.
PROG_LANG_PHRASE_PATTERNS: dict[str, list[re.Pattern]] = {
    # R (programming language)
    "rlang": [
        re.compile(r"\br\s*language\b", re.IGNORECASE),
        re.compile(r"\br\s*programming\b", re.IGNORECASE),
        re.compile(r"\bthe\s+r\s+language\b", re.IGNORECASE),
        re.compile(r"\br\s*package(s)?\b", re.IGNORECASE),
        re.compile(r"\brstudio\b", re.IGNORECASE),
        re.compile(r"\br\s*script(s)?\b", re.IGNORECASE),
        re.compile(r"\br\s*markdown\b", re.IGNORECASE),
        re.compile(r"\brmarkdown\b", re.IGNORECASE),
        re.compile(r"\bcran\b", re.IGNORECASE),
        # High-signal ecosystem terms
        re.compile(r"\btidyverse\b", re.IGNORECASE),
        re.compile(r"\bggplot2\b", re.IGNORECASE),
        re.compile(r"\bdplyr\b", re.IGNORECASE),
        re.compile(r"\bshiny\b", re.IGNORECASE),
    ],


    # C (programming language) — high precision phrase matching only (avoid Celsius, C-band, vitamin C, carbon "C", etc.)
    "clang": [
        re.compile(r"\bthe\s+c\s+language\b", re.IGNORECASE),
        re.compile(r"\bc\s+language\b", re.IGNORECASE),
        re.compile(r"\bc\s+programming\b", re.IGNORECASE),
        re.compile(r"\bansi\s+c\b", re.IGNORECASE),
        re.compile(r"\biso\s+c\b", re.IGNORECASE),
        re.compile(r"\bc\s*99\b", re.IGNORECASE),
        re.compile(r"\bc\s*11\b", re.IGNORECASE),
        re.compile(r"\bc\s*17\b", re.IGNORECASE),
        re.compile(r"\bc\s*23\b", re.IGNORECASE),
        # Toolchain mentions are strong indicators of C/C++ contexts; combined with the above, they help capture "gcc/clang" writeups.
        re.compile(r"\bgcc\b", re.IGNORECASE),
        re.compile(r"\bclang\b", re.IGNORECASE),
    ],

    # Machine code / ISA (detected via architecture mentions)
    "machinecode": [
        re.compile(r"\bx86(?:-64)?\b", re.IGNORECASE),
        re.compile(r"\bamd64\b", re.IGNORECASE),
        re.compile(r"\bx64\b", re.IGNORECASE),
        re.compile(r"\bia-32\b", re.IGNORECASE),
        re.compile(r"\baarch64\b", re.IGNORECASE),
        re.compile(r"\barmv\d+\b", re.IGNORECASE),
        re.compile(r"\brisc\s*-?\s*v\b", re.IGNORECASE),
        re.compile(r"\briscv\b", re.IGNORECASE),
        re.compile(r"\bmips\b", re.IGNORECASE),
        re.compile(r"\bpowerpc\b", re.IGNORECASE),
        re.compile(r"\bsparc\b", re.IGNORECASE),
    ],
    # C++
    "cpp": [
        re.compile(r"\bc\s*\+\s*\+\b", re.IGNORECASE),
        re.compile(r"\bc\+\+\b", re.IGNORECASE),
        re.compile(r"\bc\s*plus\s*plus\b", re.IGNORECASE),
        re.compile(r"\bcpp\b", re.IGNORECASE),
    ],

    # C#
    "csharp": [
        re.compile(r"\bc\s*#\b", re.IGNORECASE),
        re.compile(r"\bc#\b", re.IGNORECASE),
        re.compile(r"\bc\s*sharp\b", re.IGNORECASE),
        re.compile(r"\bcsharp\b", re.IGNORECASE),
    ],

    # Go
    "golang": [
        re.compile(r"\bgo\s*language\b", re.IGNORECASE),
        re.compile(r"\bgolang\b", re.IGNORECASE),
        re.compile(r"\bgo\s*programming\b", re.IGNORECASE),
    ],

    # MATLAB
    "matlab": [
        re.compile(r"\bmatlab\b", re.IGNORECASE),
        re.compile(r"\bmathworks\b", re.IGNORECASE),
    ],

    # SQL
    "sql": [
        re.compile(r"\bsql\b", re.IGNORECASE),
        re.compile(r"\bstructured\s+query\s+language\b", re.IGNORECASE),
    ],
}


# -------------------------- DISPLAY LABELS + SEARCH --------------------------
DISPLAY_LABELS = {
    "gcp": "GCP",
    "sst": "SST",
    "uhi": "UHI",
    "ndvi": "NDVI",
    "et": "ET",
    "evapotranspiration": "ET",
    "thermalinfrared": "TIR",
    "thermalir": "TIR",
    "tir": "TIR",
    "seasurfacetemperature": "Sea Surface Temperature",
    "urbanheatisland": "Urban Heat Island",

    # Pretty versions for forced merges
    "resampl": "Resample",
    "rectif": "Rectify",
    "geolocation": "Geolocation",

    # Programming languages
    "rlang": "R",
    "clang": "C",
    "cpp": "C++",
    "csharp": "C#",
    "golang": "Go",
    "matlab": "MATLAB",
    "javascript": "JavaScript",
    "typescript": "TypeScript",
    "python": "Python",
    "julia": "Julia",
    "fortran": "Fortran",
    "rust": "Rust",
    "scala": "Scala",
    "ruby": "Ruby",
    "perl": "Perl",
    "php": "PHP",
    "sql": "SQL",
    "rstudio": "RStudio",
    "rmarkdown": "R Markdown",
    "cran": "CRAN",
    "plugin": "Plugin",
    "machinecode": "Machine Code",
}

SEARCH_ALIASES = {
    "gcp": [
        "gcp", "gcps",
        "ground control point", "ground control points",
        "control point", "control points",
        "tie point", "tie points",
    ],
    "thermalinfrared": ["thermal infrared", "thermal ir", "tir", "t.i.r"],
    "seasurfacetemperature": ["sea surface temperature", "sea-surface temperature", "sst"],
    "evapotranspiration": ["evapotranspiration", "evapo transpiration", "et"],
    "urbanheatisland": ["urban heat island", "uhi"],

    # aliases for forced merges
    "resampl": ["resample", "resamples", "resampled", "resampling"],
    "rectif": ["rectify", "rectifies", "rectified", "rectifying", "rectification", "rectifications"],
    "geolocation": ["geolocation", "geolocate", "geolocated", "geolocating", "geolocates"],

    # ------------------- Programming languages -------------------
    # NOTE: R/C/C++/C#/Go are handled robustly via phrase matching during extraction;
    # these aliases help the UI search box find the right node.
    "rlang": [
        "r", "r language", "the r language", "r programming", "r package", "r packages",
        "rstudio", "r script", "r scripts", "rmarkdown", "r markdown", "cran",
        "tidyverse", "ggplot2", "dplyr", "shiny",
    ],
    "cpp": ["c++", "c plus plus", "cpp"],
    "csharp": ["c#", "c sharp", "csharp"],
    "golang": ["go", "go language", "go programming", "golang"],
    "clang": ["c", "c language", "the c language", "c programming", "ansi c", "iso c", "c99", "c11", "c17", "c23", "gcc", "clang"],
    "python": ["python", "python3", "python 3", "py"],
    "matlab": ["matlab", "mathworks"],
    "julia": ["julia"],
    "javascript": ["javascript", "js", "node", "nodejs", "node.js"],
    "typescript": ["typescript", "ts"],
    "java": ["java"],
    "fortran": ["fortran"],
    "rust": ["rust"],
    "scala": ["scala"],
    "ruby": ["ruby"],
    "perl": ["perl"],
    "php": ["php"],
    "sql": ["sql", "structured query language"],
    "machinecode": ["machine code", "binary code", "object code", "native code", "instruction set", "isa", "x86", "x86-64", "amd64", "x64", "ia-32", "aarch64", "armv7", "armv8", "risc-v", "riscv", "mips", "powerpc", "sparc"],
    "plugin": ["plugin", "plugins"],

}


# ------------------------------- HELPERS -------------------------------
def build_vocab():
    cat_vocab = {cat: {sci_stem(k) for k in kws} for cat, kws in CATEGORY_KEYWORDS.items()}
    whitelist = set().union(*cat_vocab.values())
    whitelist = {w for w in whitelist if w not in BANNED_SINGLE_STEMS}
    return cat_vocab, whitelist


def categorize(stem: str, cat_vocab) -> str | None:
    hits = [cat for cat, vocab in cat_vocab.items() if stem in vocab]
    if not hits:
        return None
    if "Georeferencing & Registration" in hits:
        return "Georeferencing & Registration"
    return hits[0]


def extract_text_from_pdf(pdf_path: str, max_pages=None) -> str:
    reader = PdfReader(pdf_path)
    n_pages = len(reader.pages)
    limit = n_pages if max_pages is None else min(n_pages, max_pages)
    chunks = []
    for i in range(limit):
        try:
            chunks.append(reader.pages[i].extract_text() or "")
        except Exception:
            pass
    return "\n".join(chunks)


def normalize_text(text: str) -> str:
    text = URL_RE.sub(" ", text)
    text = DOI_RE.sub(" ", text)
    text = EMAIL_RE.sub(" ", text)
    m = re.search(r"\n\s*references\s*\n", text, flags=re.IGNORECASE)
    if m:
        text = text[: m.start()]
    text = text.lower()
    text = re.sub(r"[\u2010\u2011\u2012\u2013\u2014]", "-", text)
    text = re.sub(r"\s+", " ", text).strip()
    return text


def stems_present_in_doc(text: str, whitelist: set, min_len: int) -> set[str]:
    """
    Document-level presence:
      - NEVER counts standalone 'point'
      - Any GCP/control/tie/ground-control point phrase adds canonical 'gcp'
      - Normal token scanning adds other whitelist stems
      - STEM_OVERRIDES force merges (resample/resampling; rectify/rectification; geolocate/geolocation)
    """
    present = set()

    if any(pat.search(text) for pat in GEO_GCP_PHRASE_PATTERNS):
        canon = sci_stem("gcp")
        if canon in whitelist:
            present.add(canon)

    # Programming language phrase matching (adds canonical stems like "rlang", "cpp", etc.)
    for canon_stem, pats in PROG_LANG_PHRASE_PATTERNS.items():
        if any(p.search(text) for p in pats):
            canon = sci_stem(canon_stem)
            if canon in whitelist:
                present.add(canon)

    toks = TOKEN_RE.findall(text)
    for t in toks:
        s = sci_stem(t)
        if len(s) < min_len:
            continue
        if s in BANNED_SINGLE_STEMS:
            continue
        if s in whitelist:
            present.add(s)

    return present


def build_matrix(words: list[str], edges: dict[tuple[str, str], int]) -> list[list[int]]:
    idx = {w: i for i, w in enumerate(words)}
    N = len(words)
    M = [[0] * N for _ in range(N)]
    for (a, b), wgt in edges.items():
        if a not in idx or b not in idx:
            continue
        i, j = idx[a], idx[b]
        M[i][j] = wgt
        M[j][i] = wgt
    return M


def max_offdiag(M: list[list[int]]) -> int:
    mx = 0
    n = len(M)
    for i in range(n):
        for j in range(i + 1, n):
            if M[i][j] > mx:
                mx = M[i][j]
    return mx


def doi_url_from_filename(basename_pdf: str) -> str | None:
    """
    Filename -> DOI URL.
    Supports:
      1) Mangled URL:
         https=]]doi.org]10.1007]s00338-024-02607-4.pdf
         -> https://doi.org/10.1007/s00338-024-02607-4
      2) Any filename containing a DOI substring starting at '10.'
    """
    base = os.path.splitext(basename_pdf)[0]
    repaired = base.replace("=", ":").replace("]", "/")
    if "doi.org/" in repaired and (repaired.startswith("http:") or repaired.startswith("https:")):
        return repaired

    if "10." in base:
        doi_part = base[base.find("10."):]
        doi_part = doi_part.replace("]", "/").replace("\\", "/")
        return "https://doi.org/" + doi_part

    return None


def strip_doi_from_display_name(filename_pdf: str) -> str:
    """
    If the filename contains a DOI (including mangled doi.org patterns), remove the DOI portion
    from what we display to the user. Keep the DOI hyperlink separately.
    """
    original = filename_pdf
    base, ext = os.path.splitext(original)
    ext = ext or ".pdf"

    cleaned = re.sub(r"^https?=\]\]doi\.org\]", "", base, flags=re.IGNORECASE)

    doi_pos = cleaned.lower().find("10.")
    if doi_pos != -1:
        cleaned = cleaned[:doi_pos]

    cleaned = re.sub(r"(doi\.org|doi)", " ", cleaned, flags=re.IGNORECASE)
    cleaned = cleaned.replace("]", " ").replace("=", " ").replace("_", " ").replace("-", " ")
    cleaned = re.sub(r"\s+", " ", cleaned).strip()

    if not cleaned:
        return original

    return f"{cleaned}{ext}"


def load_doi_citations(csv_path: str) -> dict[str, str]:
    """
    Load DOI -> full citation from a 2-column CSV:
      col 1 = full citation
      col 2 = DOI URL (e.g., https://doi.org/10.xxxx/....)
    Returns a dict with a few normalized keys per DOI to make matching robust.
    """
    mapping: dict[str, str] = {}
    if not csv_path:
        return mapping
    if not os.path.exists(csv_path):
        return mapping

    with open(csv_path, "r", encoding="utf-8-sig", newline="") as f:
        reader = csv.reader(f)
        for row in reader:
            if not row or len(row) < 2:
                continue
            citation = (row[0] or "").strip()
            doi_val = (row[1] or "").strip()
            if not citation or not doi_val:
                continue

            doi_val_norm = doi_val.strip()
            doi_val_norm = doi_val_norm.replace("http://doi.org/", "https://doi.org/")
            doi_val_norm = doi_val_norm.replace("http://dx.doi.org/", "https://doi.org/")
            doi_val_norm = doi_val_norm.replace("https://dx.doi.org/", "https://doi.org/")

            core = doi_val_norm
            if "doi.org/" in doi_val_norm:
                core = doi_val_norm.split("doi.org/", 1)[1]

            keys = {
                doi_val_norm,
                doi_val_norm.lower(),
                core,
                core.lower(),
                ("https://doi.org/" + core),
                ("https://doi.org/" + core).lower(),
            }
            for k in keys:
                mapping[k] = citation

    return mapping



def extract_year_from_citation(citation: str | None) -> int | None:
    """Try to pull a 4-digit year from a citation string, typically like '(2018)'.
    Returns the first match in 1900-2099, else None.
    """
    if not citation:
        return None
    m = re.search(r"\((19|20)\d{2}\)", citation)
    if not m:
        return None
    try:
        return int(m.group(0).strip("()"))
    except Exception:
        return None


# ---------------------- SIGNIFICANCE + EFFECT SIZE ----------------------
def _log_choose(n: int, k: int, log_fact: list[float]) -> float:
    if k < 0 or k > n:
        return float("-inf")
    return log_fact[n] - log_fact[k] - log_fact[n - k]


def hypergeom_tail_pvalue(N: int, K: int, n: int, k_obs: int, log_fact: list[float]) -> float:
    """
    One-sided enrichment p-value: P(X >= k_obs) where
      X ~ Hypergeometric(N population, K success states, n draws)
    This corresponds to Fisher's exact test (greater) on the 2x2 table.
    """
    kmax = min(K, n)
    if k_obs > kmax:
        return 0.0
    denom = _log_choose(N, n, log_fact)
    # log-sum-exp for stability
    logs = []
    for k in range(k_obs, kmax + 1):
        logs.append(_log_choose(K, k, log_fact) + _log_choose(N - K, n - k, log_fact) - denom)
    m = max(logs)
    s = sum(math.exp(x - m) for x in logs)
    p = math.exp(m) * s
    return float(min(1.0, max(0.0, p)))


def benjamini_hochberg(pvals: list[float]) -> list[float]:
    """
    Benjamini–Hochberg FDR (q-values).
    Returns q-values in the original order.
    """
    m = len(pvals)
    if m == 0:
        return []
    order = sorted(range(m), key=lambda i: pvals[i])
    q = [0.0] * m
    prev = 1.0
    for rank, i in enumerate(reversed(order), start=1):
        # reversed order gives largest p first; easier to enforce monotonicity
        p = pvals[i]
        r = m - rank + 1
        val = (p * m) / r
        if val > prev:
            val = prev
        prev = val
        q[i] = min(1.0, max(0.0, val))
    return q


def npmi(N: int, df_a: int, df_b: int, co: int) -> float:
    """
    Normalized PMI in [-1, 1].
    """
    if N <= 0 or co <= 0 or df_a <= 0 or df_b <= 0:
        return 0.0
    pxy = co / N
    px = df_a / N
    py = df_b / N
    if pxy <= 0 or px <= 0 or py <= 0:
        return 0.0
    pmi = math.log(pxy / (px * py))
    denom = -math.log(pxy)
    if denom <= 0:
        return 0.0
    return float(pmi / denom)


# ------------------------------- MAIN -------------------------------
def main():
    ap = argparse.ArgumentParser(description="Build a STEMMED document-frequency chord diagram from PDFs (D3).")
    ap.add_argument("pdf_dir", nargs="?", default=".", help="Folder with PDFs (default: .)")
    ap.add_argument("--out", default="chord.html", help="Output HTML")
    ap.add_argument("--citations", default="doi_citations.csv", help="CSV with [citation, DOI] (default: doi_citations.csv)")
    ap.add_argument("--max-pages", type=int, default=None, help="Max pages per PDF (default all)")
    ap.add_argument("--min-len", type=int, default=3, help="Min stem length")
    ap.add_argument("--min-doc-freq", type=int, default=2, help="Keep stems that appear in >= this many papers")
    ap.add_argument("--max-words-per-cat", type=int, default=12, help="Top stems per category")
    ap.add_argument("--min-edge", type=int, default=1, help="Keep edges with co-doc freq >= this")
    ap.add_argument("--max-edges", type=int, default=4000, help="Cap number of edges (strongest first)")
    args = ap.parse_args()

    doi_cite_map = load_doi_citations(args.citations)

    cat_vocab, whitelist = build_vocab()
    categories = list(CATEGORY_KEYWORDS.keys())

    pdfs = sorted(glob.glob(os.path.join(args.pdf_dir, "*.pdf")))
    if not pdfs:
        raise SystemExit(f"No PDFs found in {os.path.abspath(args.pdf_dir)}")

    paper_sets: list[set[str]] = []
    paper_files: list[str] = []
    for p in pdfs:
        paper_files.append(os.path.basename(p))
        try:
            raw = extract_text_from_pdf(p, max_pages=args.max_pages)
            present = stems_present_in_doc(normalize_text(raw), whitelist, min_len=args.min_len)
            paper_sets.append(present)
            print(f"[OK] {os.path.basename(p)} -> {len(present)} kept tokens")
        except Exception as e:
            paper_sets.append(set())
            print(f"[WARN] {os.path.basename(p)} failed: {e}")

    if sum(len(s) for s in paper_sets) < 10:
        raise SystemExit("Too few tokens extracted. (Scanned PDFs? Or vocab too strict?)")

    doc_freq = Counter()
    for s in paper_sets:
        doc_freq.update(s)

    cat_to_words = defaultdict(list)
    for stem, df in doc_freq.items():
        if df < args.min_doc_freq:
            continue
        cat = categorize(stem, cat_vocab)
        if cat:
            cat_to_words[cat].append(stem)

    edge_counts = Counter()
    for present in paper_sets:
        filtered = [s for s in present if doc_freq[s] >= args.min_doc_freq and categorize(s, cat_vocab) is not None]
        if len(filtered) < 2:
            continue
        filtered = sorted(set(filtered))
        for a, b in combinations(filtered, 2):
            edge_counts[(a, b)] += 1

    strength = Counter()
    for (a, b), w in edge_counts.items():
        strength[a] += w
        strength[b] += w

    def importance(stem: str) -> float:
        return math.log1p(doc_freq[stem]) * (1.0 + math.log1p(strength[stem]))

    for cat in list(cat_to_words.keys()):
        cat_to_words[cat].sort(key=importance, reverse=True)
        cat_to_words[cat] = cat_to_words[cat][: max(0, args.max_words_per_cat)]

    words: list[str] = []
    word_cat: dict[str, str] = {}
    cat_to_indices = defaultdict(list)

    for cat in categories:
        for w in cat_to_words.get(cat, []):
            if w not in word_cat:
                idx = len(words)
                words.append(w)
                word_cat[w] = cat
                cat_to_indices[cat].append(idx)

    if len(words) < 5:
        raise SystemExit("Too few stems after filtering. Lower --min-doc-freq or raise --max-words-per-cat.")

    kept_set = set(words)

    # edges among kept words
    edges = {}
    for (a, b), w in edge_counts.items():
        if a in kept_set and b in kept_set and w >= args.min_edge:
            edges[(a, b)] = w

    # cap strongest edges
    strongest = sorted(edges.items(), key=lambda kv: kv[1], reverse=True)[: max(0, args.max_edges)]
    edges = dict(strongest)

    raw_matrix = build_matrix(words, edges)
    max_chord = max_offdiag(raw_matrix)

    # ---------- significance + NPMI for kept edges ----------
    Ndocs = len(pdfs)
    # Precompute log factorials for hypergeom
    log_fact = [0.0] * (Ndocs + 1)
    for i in range(2, Ndocs + 1):
        log_fact[i] = log_fact[i - 1] + math.log(i)

    # build q and npmi matrices
    n_words = len(words)
    q_matrix = [[1.0] * n_words for _ in range(n_words)]
    npmi_matrix = [[0.0] * n_words for _ in range(n_words)]

    word_to_idx = {w: i for i, w in enumerate(words)}

    edge_items = []
    pvals = []
    keys = []
    for (a, b), co in edges.items():
        i = word_to_idx[a]
        j = word_to_idx[b]
        df_a = doc_freq[a]
        df_b = doc_freq[b]
        # Hypergeom params: N population, K success (df_b), n draws (df_a), observe co
        p = hypergeom_tail_pvalue(Ndocs, df_b, df_a, co, log_fact)
        pvals.append(p)
        keys.append((i, j))
        edge_items.append((i, j, co, df_a, df_b, p))

        np = npmi(Ndocs, df_a, df_b, co)
        npmi_matrix[i][j] = np
        npmi_matrix[j][i] = np

    qvals = benjamini_hochberg(pvals)
    for (i, j), qv in zip(keys, qvals):
        q_matrix[i][j] = qv
        q_matrix[j][i] = qv

    # ---------- papers payload ----------
    papers_payload = []
    for pid, (fname, present) in enumerate(zip(paper_files, paper_sets)):
        kept_indices = sorted(word_to_idx[w] for w in present.intersection(kept_set))
        doi = doi_url_from_filename(fname)
        citation_val = (
            (doi_cite_map.get(doi, None)
             or doi_cite_map.get((doi or "").lower(), None)
             or doi_cite_map.get((doi.split("doi.org/", 1)[1] if doi and "doi.org/" in doi else ""), None)
             or doi_cite_map.get((doi.split("doi.org/", 1)[1].lower() if doi and "doi.org/" in doi else ""), None))
            if doi else None
        )
        year_val = extract_year_from_citation(citation_val)
        papers_payload.append({
            "pid": pid,
            "file": fname,
            "display": strip_doi_from_display_name(fname) if doi else fname,
            "doi": doi,
            "doiCore": (doi.split("doi.org/", 1)[1] if doi and "doi.org/" in doi else None),
            "citation": citation_val,

            "year": year_val,
            "idx": kept_indices,
        })

    # ---------- category paper counts ----------
    kept_set_by_cat = defaultdict(set)
    for w in words:
        kept_set_by_cat[word_cat[w]].add(w)

    cat_paper_counts = {cat: 0 for cat in categories}
    for present in paper_sets:
        for cat in categories:
            if not kept_set_by_cat.get(cat):
                continue
            if present.intersection(kept_set_by_cat[cat]):
                cat_paper_counts[cat] += 1

    groups = []
    start = 0
    for cat in categories:
        ws = [w for w in words if word_cat[w] == cat]
        if not ws:
            continue
        end = start + len(ws)
        groups.append({
            "name": cat,
            "start": start,
            "end": end,
            "color": CATEGORY_COLORS.get(cat, "#999999"),
            "indices": cat_to_indices.get(cat, []),
            "papers": cat_paper_counts.get(cat, 0),
        })
        start = end

    display_labels = [DISPLAY_LABELS.get(w, w) for w in words]

    alias_to_stem = {}
    present_stems = set(words)
    for stem, aliases in SEARCH_ALIASES.items():
        stem_s = sci_stem(stem)
        if stem_s not in present_stems:
            continue
        for a in aliases:
            alias_to_stem[a.lower()] = stem_s

    payload = {
        "words": words,
        "displayLabels": display_labels,
        "aliasToStem": alias_to_stem,
        "wordCategory": [word_cat[w] for w in words],
        "categoryColors": CATEGORY_COLORS,
        "groups": groups,
        "matrix": raw_matrix,          # co-doc counts
        "qMatrix": q_matrix,           # FDR q-values (1.0 = not significant/unknown)
        "npmiMatrix": npmi_matrix,     # effect size
        "maxChord": max_chord,
        "nPapers": len(pdfs),
        "papers": papers_payload,
    }

    title = f"ECOSTRESS Chord Network — words={len(words)}, edges={len(edges)}, PDFs={len(pdfs)}, maxChord={max_chord}"

    html_out = """<!doctype html>
<html>
<head>
  <meta charset="utf-8"/>
  <meta name="viewport" content="width=device-width, initial-scale=1"/>
  <title>__TITLE__</title>
  <style>
    :root {
      --bg: #fff;
      --panel-bg: rgba(255,255,255,0.96);
      --text: #111;
      --hint: #333;
      --border: #ddd;
      --shadow: rgba(0,0,0,0.08);
      --row-alt: #f3f3f3;
      --btn-bg: #f6f6f6;
      --btn-border: #bbb;
      --input-bg: #fff;
      --input-border: #ccc;
	      --input-text: #111;
      --link: #0b57d0;
      --label: #111;
      --label-dim: #9a9a9a;
      --hover-chord: #000;
    }

    body.dark {
      --bg: #000;
      --panel-bg: rgba(0,0,0,0.90);
      --text: #fff;
      --hint: #ddd;
      --border: #444;
      --shadow: rgba(0,0,0,0.35);
      --row-alt: #111;
      --btn-bg: #1a1a1a;
      --btn-border: #555;
	      /* Keep form controls readable in dark mode */
	      --input-bg: #fff;
	      --input-border: #ccc;
	      --input-text: #111;
      --link: #6ea8ff;
      --label: #fff;
      --label-dim: #666;
      --hover-chord: #fff;
    }

    body { margin: 0; font-family: Arial, sans-serif; background: var(--bg); color: var(--text); }

    .panel {
      position: fixed; top: 10px; left: 10px; z-index: 10;
      background: var(--panel-bg);
      border: 1px solid var(--border); border-radius: 10px;
      padding: 8px 10px;
      box-shadow: 0 4px 18px var(--shadow);
      width: 440px;
    }

    .panelRight {
      position: fixed; top: 10px; right: 10px; z-index: 10;
      background: var(--panel-bg);
      border: 1px solid var(--border); border-radius: 10px;
      padding: 8px 10px;
      box-shadow: 0 4px 18px var(--shadow);
      width: 440px;
      max-height: calc(100vh - 20px);
      overflow: auto;
    }

    .title { font-weight:700; font-size: 12px; margin-bottom: 6px; }
    .hint { font-size: 11px; color: var(--hint); line-height: 1.25; }
    .row { display:flex; gap:6px; margin-top:6px; align-items:center; flex-wrap: wrap; }
    .row.tight { margin-top: 4px; }
    input[type="text"] {
      flex: 1; padding: 6px 8px; border: 1px solid var(--input-border); border-radius: 8px;
	      outline: none; font-size: 12px; background: var(--input-bg); color: var(--input-text);
    }
    input[type="number"], select {
      width: 120px; padding: 6px 8px; border: 1px solid var(--input-border); border-radius: 8px;
	      outline: none; font-size: 12px; background: var(--input-bg); color: var(--input-text);
    }
    #thicknessBasis { width: 180px; }
    input[type="checkbox"] { transform: translateY(1px); }
    button {
      padding: 6px 10px; border-radius: 8px; border: 1px solid var(--btn-border); background: var(--btn-bg);
      cursor:pointer; font-size: 12px; line-height: 1; color: var(--text);
    }
    .mini { padding: 6px 8px; min-width: 44px; text-align: center; }

    .legend { margin-top: 8px; padding-top: 6px; border-top: 1px solid var(--border); }
    .legend-title { font-weight: 700; font-size: 11px; margin-bottom: 4px; }
    .legend-item { display:flex; align-items:center; gap:8px; margin: 3px 0; }
    .swatch { width: 12px; height: 12px; border-radius: 3px; border: 1px solid rgba(0,0,0,0.15); }
    .legend-name { font-size: 11px; color: var(--text); flex: 1; }
    .legend-count { font-size: 11px; color: var(--hint); }

    .plistTitle { font-weight: 700; font-size: 12px; margin-bottom: 6px; }
    .plistMeta {font-size: 11px; color: var(--hint); margin-bottom: 6px; margin-top: 10px; }
    .plistTable { width: 100%; border-collapse: collapse; }
    .plistTable tr { border-top: 1px solid var(--border); }
    .plistTable td { padding: 8px 6px; font-size: 12px; vertical-align: top; }
        .paperCell.selected { box-shadow: 0 0 0 2px #111 inset; border-radius: 6px; }
.plistTable tr:nth-child(even) td { background: var(--row-alt); }
    .plistTable a,
    .panelRight a { color: var(--link); text-decoration: none; }

    .plistTable a:hover,
    .panelRight a:hover { text-decoration: underline; }

    svg { display:block; margin: 0 auto; }
    .catband { cursor: pointer; }
    .chord { fill-opacity: 0.92; stroke: none; cursor: pointer; }

    .chord.faded { pointer-events: none; }
    .label.faded { pointer-events: auto; }
    .faded { opacity: 0.24 !important; }
    .label { cursor: pointer; fill: var(--label); }
    .label.label-inactive { fill: var(--label-dim); opacity: 0.25; cursor: default; }
    .label { pointer-events: auto; user-select: none; dominant-baseline: middle; }
    .numlabel { pointer-events: none; user-select: none; dominant-baseline: middle; }
    .label-near-dim { fill: #9a9a9a; opacity: 0.24; }
    .label.faded.label-near-dim { opacity: 0.10 !important; }
    .chord.faded { opacity: 0.04 !important; }
    .label-hover { fill: var(--label); opacity: 1.0; }
    .divider { height: 1px; background: var(--border); margin-top: 8px; }

    .panelLowerLeft {
      position: fixed; left: 10px; z-index: 10;
      background: var(--panel-bg);
      border: 1px solid var(--border); border-radius: 10px;
      padding: 8px 10px;
      box-shadow: 0 4px 18px var(--shadow);
      width: 440px;
      overflow: hidden;
      display: flex;
      flex-direction: column;
      gap: 6px;
    }

    .viewerHeader {
      display:flex; align-items:center; gap:6px; flex-wrap:wrap;
    }

    .viewerTitle { font-weight:700; font-size: 12px; }
    .viewerUrl { color: var(--link); text-decoration: none; font-size: 11px; }
    .viewerUrl:hover { text-decoration: underline; }
    .githubLink { color: var(--link); text-decoration: none; }
    .githubLink:hover { text-decoration: underline; }
    .textSizer { display:flex; align-items:center; gap:4px; margin-left:auto; }
    .sizeBadge { min-width: 20px; text-align:center; font-size:11px; color: var(--hint); }
    .viewerFrameWrap {
      position: relative;
      flex: 1;
      min-height: 180px;
      border: 1px solid var(--border);
      border-radius: 8px;
      overflow: auto;
      background: var(--bg);
      color: var(--text);
    }
    .viewerMessage {
      position:absolute; inset:0;
      display:flex; align-items:center; justify-content:center;
      padding: 14px; text-align:center; font-size: 11px; color: var(--hint); line-height: 1.35;
      background: var(--bg);
      z-index: 2;
    }
    .viewerInner {
      position: relative;
      width: 100%;
      min-height: 100%;
      transform-origin: top left;
      padding: 12px;
      box-sizing: border-box;
      color: var(--text);
      background: var(--bg);
    }
    .previewSection { margin-bottom: 10px; }
    .previewLabel { font-size: 1em; font-weight: 700; color: var(--hint); text-transform: uppercase; letter-spacing: 0.03em; margin-bottom: 0.36em; }
    .previewTitle { font-size: 1.25em; font-weight: 700; line-height: 1.35; color: var(--text); margin-bottom: 0.57em; }
    .previewMeta { font-size: 1em; line-height: 1.45; color: var(--text); margin-bottom: 0.55em; }
    .previewCitation { font-size: 1em; line-height: 1.45; color: var(--text); white-space: pre-wrap; }
    .previewAbstract { font-size: 1em; line-height: 1.5; color: var(--text); white-space: pre-wrap; }
    .previewActions { display:flex; gap:8px; flex-wrap:wrap; margin-top: 8px; }
    .previewBtn {
      display:inline-flex; align-items:center; justify-content:center;
      padding: 6px 10px; border-radius: 8px; border: 1px solid var(--btn-border);
      background: var(--btn-bg); color: var(--text); text-decoration:none; font-size: 1em;
    }
    .previewBtn:hover { text-decoration: none; }
    .previewEmpty { font-size: 1em; color: var(--hint); line-height: 1.45; }
  </style>
</head>
<body class="dark">
  <div class="panel">
    <div class="title">NASA JPL ECOSTRESS Chord Network</div>
    <div class="hint">__TITLE__</div>

    <div class="row">
      <input id="search" type="text" placeholder="Search word / acronym…"/>
      <button id="findBtn" class="mini">Go</button>
    </div>

    <div class="row">
      <span class="hint" style="min-width:54px;">Label</span>
      <input id="lbl" type="number" min="3" max="60" value="6"/>
      <span class="hint" style="min-width:54px;">Dist</span>
      <input id="lblDist" type="number" min="0" max="260" value="23"/>
    </div>

    <div class="row">
      <span class="hint" style="min-width:54px;">Scale</span>
      <button id="scaleDown" class="mini">-1%</button>
      <button id="scaleUp" class="mini">+1%</button>
      <input id="scaleIn" type="number" min="5" max="300" value="55"/>
    </div>

    <div class="row">
      <span class="hint" style="min-width:110px;">Display transform</span>
      <select id="scaleMode">
        <option value="log10" selected>log10</option>
        <option value="linear">linear</option>
      </select>
      <span class="hint">(auto)</span>
    </div>
    <div class="row">
      <span class="hint" style="min-width:110px;">Edge metric</span>
      <select id="thicknessBasis">
        <option value="count" selected>Count (co-occurrence)</option>
        <option value="npmi">Association (NPMI)</option>
        <option value="q">Significance (−log10 q)</option>
      </select>
      <span class="hint">(chord thickness)</span>
    </div>


    <div class="row">
      <div style="flex:1; display:flex; align-items:center; gap:6px;">
        <span class="hint" style="min-width:54px;">Outline</span>
        <input id="outlineW" type="number" min="0" max="8" step="0.2" value="0.2" style="flex:1;"/>
      </div>

      <div style="flex:1; display:flex; align-items:center; gap:6px;">
        <span class="hint" style="min-width:54px;">Color</span>
        <select id="outlineColor" style="flex:1;">
          <option value="#ffffff">White</option>
          <option value="#000000" selected>Black</option>
        </select>
      </div>
    </div>

    <div class="divider"></div>
    <div class="row tight">
      <label class="hint" style="min-width:120px; display:flex; gap:6px; align-items:center;">
        <input id="sigToggle" type="checkbox"/>
        Significant only
      </label>
      <span class="hint" style="min-width:54px;">q ≤</span>
      <input id="qThresh" type="number" min="0" max="1" step="0.01" value="0.05"/>
      <span class="hint" style="flex:1;">FDR</span>
    </div>

<div class="row tight" style="margin-top:6px;">
  <span class="hint" style="min-width:120px;">Normalization</span>
  <select id="chordScaleMode" style="flex:1;">
    <option value="global" selected>Global (all edges)</option>
    <option value="active">Active (highlighted edges)</option>
  </select>
</div>

    <div class="divider"></div>
    <div class="row tight" style="margin-top:6px;">
      <label class="hint" style="min-width:120px; display:flex; gap:6px; align-items:center;">
        <input id="showCatNums" type="checkbox"/>
        Category numbers
      </label>
      <span class="hint" style="min-width:54px;">Size</span>
      <input id="catNumSize" type="number" min="4" max="42" value="10" style="width:60px;"/>
      <span class="hint" style="min-width:54px;">Color</span>
      <input id="catNumColor" type="color" value="#ffffff" style="width:60px;"/>
    </div>
    <div class="row tight" style="margin-top:6px;">
      <label class="hint" style="min-width:120px; display:flex; gap:6px; align-items:center;">
        <input id="showWordNums" type="checkbox"/>
        Word numbers
      </label>
      <span class="hint" style="min-width:54px;">Size</span>
      <input id="wordNumSize" type="number" min="4" max="42" value="9" style="width:60px;"/>
      <span class="hint" style="min-width:54px;">Color</span>
      <input id="wordNumColor" type="color" value="#ffffff" style="width:60px;"/>
    </div>
    <div class="divider"></div>

    <div class="legend" id="legend"></div>

    <div class="row">
      <button id="resetBtn" class="mini" style="flex:1;">Reset</button>
    </div>

    <div class="row">
      <button id="lightModeBtn" class="mini" style="flex:1;">Light Mode</button>
      <button id="darkModeBtn" class="mini" style="flex:1;">Dark Mode</button>
    </div>

    <div class="row" style="margin-top:8px; display:block;">
      <div class="hint" style="line-height:1.4;">
        <strong>Cite as:</strong> Longenecker, J. (2026). <em>Literature review chord network analysis tool</em>. <a class="githubLink" href="https://github.com/jakelongenecker93/Literature-Review-Chord-Diagram-Search/tree/main" target="_blank" rel="noopener noreferrer">GitHub</a>
      </div>
    </div>
  </div>

  <div class="panelLowerLeft" id="paperViewerPanel">
    <div class="viewerHeader">
      <div class="viewerTitle">Paper Viewer</div>
      <div class="textSizer">
        <span class="hint">Text</span>
        <button id="paperTextDown" class="mini" type="button">-</button>
        <span id="paperTextValue" class="sizeBadge">8</span>
        <button id="paperTextUp" class="mini" type="button">+</button>
      </div>
    </div>
    <div class="viewerFrameWrap" id="paperViewerWrap">
      <div id="paperViewerMessage" class="viewerMessage">Click a paper citation to load a local preview with metadata, citation, and abstract here.</div>
      <div id="paperViewerInner" class="viewerInner"></div>
    </div>
  </div>

  <div class="panelRight">
    <div class="plistTitle">ECOSTRESS Papers</div>
    <div class="row" style="margin-top:6px;">
      <input id="paperSearch" type="text" placeholder="Search citations…"/>
      <button id="paperSearchClear" class="mini">Clear</button>
    </div>

    <div class="row tight" style="margin-top:6px; gap:5px; flex-wrap:nowrap; align-items:center;">
      <label class="hint" style="min-width:96px; display:flex; gap:5px; align-items:center; white-space:nowrap;">
        <input id="yearFilterToggle" type="checkbox"/>
        Year filter
      </label>
      <label class="hint" style="min-width:88px; display:flex; gap:5px; align-items:center; opacity:0.65; white-space:nowrap; margin-right:2px;" id="singleYearWrap">
        <input id="singleYearToggle" type="checkbox" disabled/>
        Single Year
      </label>
      <input id="minYear" type="number" placeholder="Start" style="width:64px;"/>
      <input id="maxYear" type="number" placeholder="End" style="width:64px;"/>
      <span class="hint" style="white-space:nowrap;">(from citation)</span>
    </div>
    <div id="plistMeta" class="plistMeta">Click a category, word, or chord to list matching PDFs.</div>
    <table id="plistTable" class="plistTable"></table>
  </div>

  <div id="vis"></div>

  <script src="https://d3js.org/d3.v7.min.js"></script>
  <script>
    const DATA = __PAYLOAD__;
    const words = DATA.words;
    const displayLabels = DATA.displayLabels || words;
    const baseCountMatrix = DATA.matrix;
    let rawCountMatrix = baseCountMatrix;
    const qMatrix = DATA.qMatrix || null;
    const npmiMatrix = DATA.npmiMatrix || null;

    let maxChordDetected = Math.max(1, DATA.maxChord || 1);
    const groups = DATA.groups;
    const allPapers = DATA.papers || [];
    let papers = allPapers.slice();
    let activePapers = papers;
    const aliasToStem = DATA.aliasToStem || {};

    const stemToIndex = new Map(words.map((w,i)=>[String(w).toLowerCase(), i]));

    let thicknessMode = "log10";
    let thicknessBasis = "count"; // count | npmi | q
    let outlineWidth = 0.2;
    let outlineColor = "#000000";

    // Optional numeric labels (counts/association/significance aggregated over visible edges)
    let showWordNums = false;
    let showCatNums = false;
    let wordNumSize = 9;
    let catNumSize = 10;
    let wordNumColor = "#ffffff";
    let catNumColor = "#ffffff";
    let diagramScale = 0.55;
    let labelSize = 6;
    let labelOffset = 23;
    let sigOnly = false;
    let qThresh = 0.05;

// Normalization: global (all data) vs active (rescale highlighted chords only)
let chordScaleMode = "global";
// Hard-coded geometry output range when using "Active" scaling mode.
// This intentionally exaggerates differences among very-thin highlighted chords.
const ACTIVE_GEOM_MIN = 10;
const ACTIVE_GEOM_MAX = 4000;

    let geomMatrix = null;
    let chords = null;

    const width = 980, height = 980;
    const HOVER_GROW = 1.55;
    const HOVER_DIM_NEIGHBORS = 6;

    function clamp(v, lo, hi) { return Math.max(lo, Math.min(hi, v)); }

    function computeRadii() {
      const baseOuter = Math.min(width, height) * 0.44;
      const outerRadius = baseOuter * diagramScale * 0.97;
      const innerRadius = outerRadius - 28;
      return { outerRadius, innerRadius };
    }

    const svg = d3.select("#vis").append("svg")
      .attr("viewBox", [-width/2, -height/2, width, height]);

    const root = svg.append("g");

    const colorByIndex = (i) => {
      const cat = DATA.wordCategory[i];
      return DATA.categoryColors[cat] || "#999";
    };

    const chordLayout = d3.chord()
      .padAngle(0.006)
      .sortSubgroups(d3.descending)
      .sortChords(d3.descending);

    const GEOM_MAX = 1000;

function mapWeightWithMax(w, maxV, outMin=0, outMax=GEOM_MAX){
  if (w <= 0) return 0;
  const mv = Math.max(1, maxV || 1);
  if (thicknessMode === "linear") {
    const x = Math.min(1, w / mv);
    return outMin + x * (outMax - outMin);
  } else {
    const denom = Math.log10(mv + 1);
    const x = Math.min(1, Math.log10(w + 1) / denom);
    return outMin + x * (outMax - outMin);
  }
}

function mapWeight(w){
  return mapWeightWithMax(w, maxChordDetected, 0, GEOM_MAX);
}

    function buildWorkingCountMatrix(){
      const n = rawCountMatrix.length;
      const M = Array.from({length:n}, ()=>Array(n).fill(0));
      for (let i=0;i<n;i++){
        for (let j=0;j<n;j++){
          let v = rawCountMatrix[i][j];
          if (sigOnly && qMatrix) {
            const q = qMatrix[i][j];
            if (!(q <= qThresh)) v = 0;
          }
          M[i][j] = v;
        }
      }
      return M;
    }


    function buildWorkingWeightMatrix(){
      // Start from the (optionally) significance-filtered count matrix so the "Significant only"
      // toggle still removes edges regardless of thickness basis.
      const countM = buildWorkingCountMatrix();
      const n = countM.length;
      const W = Array.from({length:n}, ()=>Array(n).fill(0));

      for (let i=0;i<n;i++){
        for (let j=0;j<n;j++){
          const c = countM[i][j];
          if (c <= 0) { W[i][j] = 0; continue; }

          if (thicknessBasis === "npmi") {
            const np = (npmiMatrix ? npmiMatrix[i][j] : 0);
            // NPMI is [-1, 1]; use only positive association strength for thickness.
            W[i][j] = Math.max(0, np || 0);
          } else if (thicknessBasis === "q") {
            // Smaller q = stronger evidence. Convert to a positive score.
            let q = (qMatrix ? qMatrix[i][j] : 1.0);
            if (q === null || q === undefined) q = 1.0;
            q = Math.max(1e-12, Math.min(1.0, q));
            W[i][j] = -Math.log10(q); // 0 .. 12-ish
          } else {
            // default: count
            W[i][j] = c;
          }
        }
      }
      return W;
    }

    function maxOffDiagFloat(M){
      let mx = 0;
      const n = M.length;
      for (let i=0;i<n;i++){
        for (let j=i+1;j<n;j++){
          const v = M[i][j];
          if (v > mx) mx = v;
        }
      }
      return mx;
    }

function getDrilldownLayers(sel){
  if (!sel) return [];
  if (sel.kind === "combo" && Array.isArray(sel.layers)) return sel.layers.slice();
  return [sel];
}

function selectionIndexSet(sel){
  if (!sel) return new Set();
  if (sel.kind === "pair") return new Set(sel.pair || []);
  if (sel.kind === "combo") {
    const out = new Set();
    for (const layer of getDrilldownLayers(sel)) {
      for (const idx of selectionIndexSet(layer)) out.add(idx);
    }
    return out;
  }
  if (Array.isArray(sel.indices)) return new Set(sel.indices);
  return new Set();
}

function selectionHasIndex(sel, idx){
  return selectionIndexSet(sel).has(idx);
}

function isWordOrCategorySelection(sel){
  return !!sel && (sel.kind === "word" || sel.kind === "category");
}

function paperMatchesBasicSelection(p, sel){
  const idxArr = p.idx || [];
  if (!sel) return false;

  if (sel.kind === "pair") {
    const [i, j] = sel.pair;
    let hasI = false, hasJ = false;
    for (const x of idxArr) {
      if (x === i) hasI = true;
      if (x === j) hasJ = true;
      if (hasI && hasJ) return true;
    }
    return false;
  }

  if (sel.kind === "word") {
    const i = sel.indices[0];
    return idxArr.includes(i);
  }

  if (sel.kind === "paper") {
    return (p.pid === sel.pid);
  }

  if (sel.kind === "category") {
    const set = new Set(sel.indices);
    for (const x of idxArr) {
      if (set.has(x)) return true;
    }
    return false;
  }

  return false;
}

function selectionsOverlap(a, b){
  const aSet = selectionIndexSet(a);
  const bSet = selectionIndexSet(b);
  for (const idx of aSet) {
    if (bSet.has(idx)) return true;
  }
  return false;
}

function layersAreConnected(leftSel, rightSel, work){
  const left = Array.from(selectionIndexSet(leftSel));
  const right = Array.from(selectionIndexSet(rightSel));
  if (!left.length || !right.length) return false;

  for (const a of left) {
    for (const b of right) {
      if (a === b) continue;
      if ((work[a] && work[a][b] > 0) || (work[b] && work[b][a] > 0)) {
        return true;
      }
    }
  }
  return false;
}

function finalizeComboLayers(layers){
  if (!layers || !layers.length) return null;
  if (layers.length === 1) return layers[0];
  return {
    kind: "combo",
    layers,
    indices: Array.from(new Set(layers.flatMap(layer => Array.from(selectionIndexSet(layer)))))
  };
}

function makeDrilldownSelection(baseSel, nextSel){
  if (!isWordOrCategorySelection(nextSel)) return nextSel;
  if (!isWordOrCategorySelection(baseSel) && !(baseSel && baseSel.kind === "combo")) {
    return nextSel;
  }

  const layers = getDrilldownLayers(baseSel);
  if (!layers.length) return nextSel;

  const work = buildWorkingCountMatrix();
  const nextIndices = Array.from(selectionIndexSet(nextSel));
  if (!nextIndices.length) return nextSel;

  const prevLayer = layers[layers.length - 1];
  const prevIndices = Array.from(selectionIndexSet(prevLayer));
  const sameAsPrev = (prevIndices.length === nextIndices.length) && prevIndices.every(v => nextIndices.includes(v));
  if (sameAsPrev) return nextSel;

  // If the new selection overlaps one of the existing layers, refine that layer in place
  // instead of merely appending a new layer. This lets a category→category selection
  // drill down into word→category (or category→word) within the chord chart.
  for (let idx = layers.length - 1; idx >= 0; idx--) {
    if (!selectionsOverlap(layers[idx], nextSel)) continue;

    const candidate = layers.slice();
    candidate[idx] = nextSel;

    let valid = true;
    for (let k = 0; k < candidate.length - 1; k++) {
      if (!layersAreConnected(candidate[k], candidate[k + 1], work)) {
        valid = false;
        break;
      }
    }

    if (valid) return finalizeComboLayers(candidate);
  }

  if (!layersAreConnected(prevLayer, nextSel, work)) return nextSel;

  const nextLayers = layers.concat([nextSel]);
  if (nextLayers.length > 30) return nextSel;
  return finalizeComboLayers(nextLayers);
}

function edgeIsHighlighted(i, j, sel){
  if (!sel) return false;

  if (sel.kind === "combo") {
    const keep = selectionIndexSet(sel);
    return keep.has(i) && keep.has(j);
  }

  if (sel.kind === "pair") {
    const a = sel.pair[0], b = sel.pair[1];
    return (i === a && j === b) || (i === b && j === a);
  }

  const keep = selectionIndexSet(sel);
  if (sel.kind === "paper") {
    return keep.has(i) && keep.has(j);
  }

  // word/category: chord highlighted if it touches any kept endpoint
  return keep.has(i) || keep.has(j);
}

function rebuildGeomMatrix(selForActive=null){
  const workCount = buildWorkingCountMatrix();
  const workW = buildWorkingWeightMatrix();
  const n = workW.length;
  const globalMaxW = Math.max(1e-12, maxOffDiagFloat(workW) || 1);
  geomMatrix = Array.from({length:n}, () => Array(n).fill(0));

  if (chordScaleMode === "active" && selForActive) {
    // Find max raw weight among highlighted edges (respecting sig filter)
    let activeMaxW = 1;
    for (let i=0;i<n;i++){
      for (let j=0;j<n;j++){
        const v = workW[i][j];
        if (v > 0 && edgeIsHighlighted(i, j, selForActive)) {
          if (v > activeMaxW) activeMaxW = v;
        }
      }
    }

    for (let i=0;i<n;i++){
      for (let j=0;j<n;j++){
        const v = workW[i][j];
        if (v <= 0) { geomMatrix[i][j] = 0; continue; }
        if (edgeIsHighlighted(i, j, selForActive)) {
          geomMatrix[i][j] = mapWeightWithMax(v, activeMaxW, ACTIVE_GEOM_MIN, ACTIVE_GEOM_MAX);
        } else {
          geomMatrix[i][j] = mapWeightWithMax(v, globalMaxW, 0, GEOM_MAX);
        }
      }
    }
  } else {
    for (let i=0;i<n;i++){
      for (let j=0;j<n;j++){
        geomMatrix[i][j] = mapWeightWithMax(workW[i][j], globalMaxW, 0, GEOM_MAX);
      }
    }
  }

  chords = chordLayout(geomMatrix);
}

rebuildGeomMatrix(null);

    let currentHighlight = null;
let currentSelection = null;
let selectedPaperPid = null;
    let paperQuery = "";
    let paperViewerTextSize = 12;
    let activePaperUrl = "";
    const paperPreviewCache = new Map();
    let arcPaths = null;
    let chordPathsSel = null;
    let labelsSel = null;

    let hoverChord = null;
    let currentHoverSelection = null;

    // Tracks which words have >=1 active edge after all filters (year + significance + thickness basis)
    // Used to dim inactive labels and prevent "empty" selections.
    let currentHasAny = null;

    function paperMatchesSelection(p, sel){
      if (!sel) return false;
      if (sel.kind === "combo") {
        return getDrilldownLayers(sel).every(layer => paperMatchesBasicSelection(p, layer));
      }
      return paperMatchesBasicSelection(p, sel);
    }


function escapeHtml(text){
  return String(text || "")
    .replace(/&/g, "&amp;")
    .replace(/</g, "&lt;")
    .replace(/>/g, "&gt;")
    .replace(/"/g, "&quot;")
    .replace(/'/g, "&#39;");
}

function stripHtmlTags(text){
  const div = document.createElement("div");
  div.innerHTML = String(text || "");
  return (div.textContent || div.innerText || "").replace(/\s+/g, " ").trim();
}

function decodeCrossrefAbstract(text){
  if (!text) return "";
  return stripHtmlTags(String(text).replace(/<\/?jats:[^>]+>/gi, " "));
}

function invertOpenAlexAbstract(indexObj){
  if (!indexObj || typeof indexObj !== "object") return "";
  const entries = Object.entries(indexObj);
  if (!entries.length) return "";
  const maxPos = Math.max(...entries.flatMap(([, positions]) => Array.isArray(positions) ? positions : []), -1);
  if (maxPos < 0) return "";
  const words = Array(maxPos + 1).fill("");
  for (const [word, positions] of entries) {
    if (!Array.isArray(positions)) continue;
    for (const pos of positions) {
      if (Number.isInteger(pos) && pos >= 0 && pos < words.length) words[pos] = word;
    }
  }
  return words.join(" ").replace(/\s+/g, " ").trim();
}

function normalizeAuthors(authorList){
  if (!Array.isArray(authorList) || !authorList.length) return "";
  return authorList
    .map(a => {
      if (!a) return "";
      if (typeof a === "string") return a.trim();
      const given = (a.given || a.first_name || "").trim();
      const family = (a.family || a.last_name || "").trim();
      const literal = (a.name || a.literal || a.author || "").trim();
      return literal || [given, family].filter(Boolean).join(" ");
    })
    .filter(Boolean)
    .join(", ");
}

function getPaperPreviewFallback(p){
  const citationText = ((p && p.citation) || "").trim();
  const title = ((p && (p.display || p.file || p.doiCore || "Untitled paper")) || "Untitled paper").trim();
  return {
    title,
    citation: citationText,
    authors: "",
    journal: "",
    year: (p && p.year) ? String(p.year) : "",
    abstract: "Abstract not available from the current metadata source.",
    source: "fallback",
    openUrl: (p && p.doi) ? p.doi : ""
  };
}

async function fetchCrossrefPreview(doiCore){
  const url = `https://api.crossref.org/works/${encodeURIComponent(doiCore)}`;
  const res = await fetch(url, { headers: { "Accept": "application/json" } });
  if (!res.ok) throw new Error(`Crossref ${res.status}`);
  const payload = await res.json();
  const msg = payload && payload.message ? payload.message : {};
  return {
    title: (Array.isArray(msg.title) && msg.title[0]) ? msg.title[0] : "",
    authors: normalizeAuthors(msg.author || []),
    journal: (Array.isArray(msg["container-title"]) && msg["container-title"][0]) ? msg["container-title"][0] : "",
    year: String(msg.issued && msg.issued["date-parts"] && msg.issued["date-parts"][0] && msg.issued["date-parts"][0][0] || "").trim(),
    abstract: decodeCrossrefAbstract(msg.abstract || ""),
    citation: "",
    source: "crossref",
    openUrl: (Array.isArray(msg.link) && msg.link[0] && msg.link[0].URL) ? msg.link[0].URL : ""
  };
}

async function fetchOpenAlexPreview(doiCore){
  const url = `https://api.openalex.org/works/https://doi.org/${encodeURIComponent(doiCore)}`;
  const res = await fetch(url, { headers: { "Accept": "application/json" } });
  if (!res.ok) throw new Error(`OpenAlex ${res.status}`);
  const msg = await res.json();
  return {
    title: (msg.title || "").trim(),
    authors: Array.isArray(msg.authorships) ? msg.authorships.map(a => a && a.author ? a.author.display_name : "").filter(Boolean).join(", ") : "",
    journal: (msg.primary_location && msg.primary_location.source && msg.primary_location.source.display_name) ? msg.primary_location.source.display_name : "",
    year: msg.publication_year ? String(msg.publication_year) : "",
    abstract: invertOpenAlexAbstract(msg.abstract_inverted_index || {}),
    citation: "",
    source: "openalex",
    openUrl: (msg.primary_location && msg.primary_location.landing_page_url) ? msg.primary_location.landing_page_url : `https://doi.org/${doiCore}`
  };
}

async function getPaperPreviewData(p){
  const fallback = getPaperPreviewFallback(p);
  const doiCore = ((p && p.doiCore) || "").trim();
  const cacheKey = doiCore || `pid:${p && p.pid}`;
  if (paperPreviewCache.has(cacheKey)) {
    const cached = paperPreviewCache.get(cacheKey);
    return { ...fallback, ...cached, citation: fallback.citation || cached.citation || "", openUrl: (p && p.doi) ? p.doi : (cached.openUrl || "") };
  }

  let data = {};
  if (doiCore) {
    try {
      data = await fetchCrossrefPreview(doiCore);
    } catch (err) {
      try {
        data = await fetchOpenAlexPreview(doiCore);
      } catch (err2) {
        data = {};
      }
    }
  }

  const merged = {
    ...fallback,
    ...data,
    citation: fallback.citation || data.citation || "",
    openUrl: (p && p.doi) ? p.doi : (data.openUrl || fallback.openUrl || "")
  };
  if (!merged.abstract) merged.abstract = fallback.abstract;
  if (!merged.title) merged.title = fallback.title;
  paperPreviewCache.set(cacheKey, merged);
  return merged;
}

function renderPaperPreview(preview, p){
  const inner = document.getElementById("paperViewerInner");
  const msgEl = document.getElementById("paperViewerMessage");
  const linkEl = document.getElementById("paperViewerLink");
  if (!inner || !msgEl) return;

  const citationText = (preview.citation || ((p && p.citation) || "")).trim();
  const title = (preview.title || ((p && (p.display || p.file)) || "Untitled paper")).trim();
  const authors = (preview.authors || "").trim();
  const metaBits = [preview.journal, preview.year].filter(Boolean);
  const abstractText = (preview.abstract || "").trim();
  const abstractHtml = abstractText
    ? escapeHtml(abstractText)
    : '<div class="previewEmpty">Abstract not available from the current metadata source.</div>';

  inner.innerHTML = `
    <div class="previewSection">
      <div class="previewLabel">Title</div>
      <div class="previewTitle">${escapeHtml(title)}</div>
    </div>
    ${authors ? `<div class="previewSection"><div class="previewLabel">Authors</div><div class="previewMeta">${escapeHtml(authors)}</div></div>` : ""}
    ${metaBits.length ? `<div class="previewSection"><div class="previewLabel">Journal</div><div class="previewMeta">${escapeHtml(metaBits.join(" · "))}</div></div>` : ""}
    ${citationText ? `<div class="previewSection"><div class="previewLabel">Citation</div><div class="previewCitation">${escapeHtml(citationText)}</div></div>` : ""}
    <div class="previewSection">
      <div class="previewLabel">Abstract</div>
      <div class="previewAbstract">${abstractHtml}</div>
    </div>
    ${(preview.openUrl || (p && p.doi)) ? `<div class="previewActions"><a class="previewBtn" href="${escapeHtml(preview.openUrl || p.doi)}" target="_blank" rel="noopener noreferrer">Open full paper</a></div>` : ""}
  `;

  if (linkEl) {
    if (preview.openUrl || (p && p.doi)) {
      linkEl.href = preview.openUrl || p.doi;
      linkEl.style.display = "inline";
    } else {
      linkEl.removeAttribute("href");
      linkEl.style.display = "none";
    }
  }
  msgEl.style.display = "none";
  applyPaperViewerTextSize();
}

function applyPaperViewerTextSize(){
  const valEl = document.getElementById("paperTextValue");
  const inner = document.getElementById("paperViewerInner");
  if (valEl) valEl.textContent = String(paperViewerTextSize);
  if (!inner) return;
  inner.style.fontSize = `${paperViewerTextSize}px`;
}

function setPaperViewerMessage(msg){
  const msgEl = document.getElementById("paperViewerMessage");
  const inner = document.getElementById("paperViewerInner");
  if (msgEl) {
    msgEl.textContent = msg;
    msgEl.style.display = "flex";
  }
  if (inner) inner.innerHTML = "";
}

async function openPaperViewer(p){
  const linkEl = document.getElementById("paperViewerLink");

  if (!p) {
    activePaperUrl = "";
    if (linkEl) linkEl.style.display = "none";
    setPaperViewerMessage("No paper is currently selected.");
    return;
  }

  activePaperUrl = p.doi || "";
  if (linkEl) {
    if (p.doi) {
      linkEl.href = p.doi;
      linkEl.style.display = "inline";
    } else {
      linkEl.style.display = "none";
    }
  }

  setPaperViewerMessage("Loading local preview…");
  try {
    const preview = await getPaperPreviewData(p);
    if (selectedPaperPid !== p.pid) return;
    renderPaperPreview(preview, p);
  } catch (err) {
    if (selectedPaperPid !== p.pid) return;
    renderPaperPreview(getPaperPreviewFallback(p), p);
  }
}

function layoutLowerLeftPanel(){
  const topPanel = document.querySelector('.panel');
  const lowerPanel = document.getElementById('paperViewerPanel');
  if (!topPanel || !lowerPanel) return;
  const rect = topPanel.getBoundingClientRect();
  const top = Math.round(rect.bottom + 10);
  const height = Math.max(180, Math.round(window.innerHeight - top - 10));
  lowerPanel.style.top = `${top}px`;
  lowerPanel.style.height = `${height}px`;
}

function renderPapersList(sel){
  const table = document.getElementById("plistTable");
  const meta = document.getElementById("plistMeta");

  table.innerHTML = "";

  if (!sel) {
    // Default view: show all papers (so search works immediately)
  }

  const matches = sel ? papers.filter(p => paperMatchesSelection(p, sel)) : papers.slice();
  const q = (paperQuery || "").trim().toLowerCase();
  const shown = (!q) ? matches : matches.filter(p => {
    const citationText = (p.citation || "").trim();
    const fallbackTitle = (p.display || p.file || "").trim();
    const blob = `${citationText} ${fallbackTitle} ${(p.doiCore||"")} ${(p.doi||"")}`.toLowerCase();
    return blob.includes(q);
  });

  const baseLabel = sel ? "matching papers" : "papers";
  meta.textContent = q
    ? `${shown.length} of ${matches.length} ${baseLabel}`
    : (sel ? `${matches.length} ${baseLabel}` : `All ${matches.length} ${baseLabel} (click a category, word, or chord to filter)`);

  for (const p of shown) {
    const tr = document.createElement("tr");
    const td = document.createElement("td");
    td.classList.add("paperCell");
    if (selectedPaperPid !== null && selectedPaperPid === p.pid) td.classList.add("selected");

    const citationText = (p.citation || "").trim();
    const fallbackTitle = (p.display || p.file || "").trim();
    const left = citationText ? citationText : fallbackTitle;

    const span = document.createElement("span");
    span.textContent = left;
    span.style.cursor = "pointer";
    span.title = "Click to highlight chords for this paper and load its local preview below";
    span.addEventListener("click", (ev) => {
      ev.stopPropagation();
      selectedPaperPid = p.pid;
      currentHighlight = { kind: "paper", pid: p.pid, indices: (p.idx || []) };
      openPaperViewer(p);
      if (chordScaleMode === "active") { rerenderForHighlightOnly(currentHighlight); return; }
      // In global normalization, highlight changes must still update dependent overlays
      // (numeric labels + empty-category hatch), so re-render using the current matrix.
      render();
    });

    td.appendChild(span);

    if (p.doi) {
      const a = document.createElement("a");
      a.href = p.doi;
      a.target = "_blank";
      a.rel = "noopener noreferrer";
      a.textContent = p.doi;

      td.appendChild(document.createTextNode(" "));
      td.appendChild(a);
    }

    tr.appendChild(td);
    table.appendChild(tr);
  }
}

    function resetHighlightState() {
      // Reset plot/selection state, but KEEP any citation search text
      // so the user can continue searching immediately.
      currentHighlight = null;
      currentSelection = null;
      currentHoverSelection = null;
      selectedPaperPid = null;
      activePaperUrl = "";
      const linkEl = document.getElementById("paperViewerLink");
      if (linkEl) linkEl.style.display = "none";
      setPaperViewerMessage("Click a paper citation to load a local preview with metadata, citation, and abstract here.");

      if (hoverChord) hoverChord.attr("display", "none");

      // Force a full re-render in BOTH modes so dependent overlays
      // (crosshatch, numeric labels, etc.) are rebuilt immediately.
      if (chordScaleMode === "active") {
        rerenderWithNewEdges();
        return;
      }

      render();
      renderPapersList(null);
    }

    function applySelectedEndpointStyles() {
      if (arcPaths) {
        arcPaths
          .style("stroke", outlineColor)
          .style("stroke-width", outlineWidth);
      }

      if (chordPathsSel) {
        chordPathsSel
          .style("stroke", null)
          .style("stroke-width", null)
          .style("paint-order", null);
      }

      clearLabelHoverStyles();

      const sel = currentHighlight || currentSelection || null;
      if (!sel || !labelsSel || !arcPaths) return;

      let keep = null;
      if (sel.kind === "pair") {
        keep = new Set(sel.pair || []);
      } else {
        return;
      }

      labelsSel
        .filter(d => keep.has(d.index))
        .classed("label-hover", true)
        .attr("font-size", Math.round(labelSize * HOVER_GROW))
        .style("fill", "var(--label)");

      arcPaths
        .filter(d => keep.has(d.index))
        .style("stroke", "var(--hover-chord)")
        .style("stroke-width", outlineWidth + 1);

      if (chordPathsSel) {
        chordPathsSel
          .filter(d => {
            const a = d.source.index, b = d.target.index;
            return (keep.has(a) && keep.has(b));
          })
          .style("stroke", "var(--hover-chord)")
          .style("stroke-width", outlineWidth + 1)
          .style("paint-order", "stroke fill");
      }
    }

    function applyCurrentHighlightState() {
      applyHighlight(currentHoverSelection || currentHighlight || null);
      if (!currentHoverSelection) applySelectedEndpointStyles();
    }

    function clearChordHoverStyles() {
      if (!chordPathsSel) return;

      chordPathsSel
        .style("fill", null)
        .style("stroke", null)
        .style("stroke-width", null)
        .style("fill-opacity", null);

      if (hoverChord) hoverChord.attr("display", "none");
    }

    function applyConnectedChordHover(sel) {
      if (!chordPathsSel) return;

      clearChordHoverStyles();

      if (!sel) return;

      chordPathsSel.filter(d => {
        const i = d.source.index;
        const j = d.target.index;
        return edgeIsHighlighted(i, j, sel);
      })
      .style("fill", "var(--hover-chord)");
    }

    function setHoverSelection(sel) {
      currentHoverSelection = sel;

      // Hover should not drive faded/non-faded state.
      // Keep the current click-selection view exactly as-is.
      applyHighlight(currentHighlight || currentSelection || null);

      // Clear any prior hover-only recoloring first, then re-apply the
      // persistent click-selection styling so the selected chord outline
      // never disappears when hover state changes.
      clearChordHoverStyles();
      applySelectedEndpointStyles();

      // Add hover-only chord recoloring without dimming other chords.
      if (sel) applyConnectedChordHover(sel);
    }

    function applyHighlight(sel) {
      if(!arcPaths || !labelsSel || !chordPathsSel) return;

      // Use the *current* effective matrix for neighborhood checks
      const work = buildWorkingCountMatrix();

      if(!sel) {
        chordPathsSel.classed("faded", false);
        arcPaths.classed("faded", false);
        labelsSel.classed("faded", false);
        return;
      }

      if(sel.kind === "pair") {
        const i = sel.pair[0], j = sel.pair[1];
        const keepWords = new Set([i, j]);

        for (let k = 0; k < work.length; k++) {
          if (k === i || k === j) continue;
          if (work[i][k] > 0 || work[k][i] > 0 || work[j][k] > 0 || work[k][j] > 0) {
            keepWords.add(k);
          }
        }

        // Keep all chords touching either endpoint
        chordPathsSel.classed("faded", d => {
          const a = d.source.index, b = d.target.index;
          return !(a === i || a === j || b === i || b === j);
        });

        // Keep the selected endpoints lit, and also keep any words that are
        // directly connected to either endpoint visible (but not white outlined).
        arcPaths.classed("faded", d => !keepWords.has(d.index));
        labelsSel.classed("faded", d => !keepWords.has(d.index));
        return;
      }

      if (sel.kind === "combo") {
        const keepWords = new Set();
        chordPathsSel.classed("faded", d => {
          const a = d.source.index, b = d.target.index;
          const keepEdge = edgeIsHighlighted(a, b, sel);
          if (keepEdge) {
            keepWords.add(a);
            keepWords.add(b);
          }
          return !keepEdge;
        });

        const selectedWords = selectionIndexSet(sel);
        for (const idx of selectedWords) keepWords.add(idx);

        arcPaths.classed("faded", d => !keepWords.has(d.index));
        labelsSel.classed("faded", d => !keepWords.has(d.index));
        return;
      }

      const keep = new Set(sel.indices);

      // For a paper selection: show ONLY chords where BOTH endpoints are in the paper.
      // For category selection: show chords touching any kept endpoint (original behavior).
      const chordKeepFn = (sel.kind === "paper")
        ? (d => (keep.has(d.source.index) && keep.has(d.target.index)))
        : (d => (keep.has(d.source.index) || keep.has(d.target.index)));

      chordPathsSel.classed("faded", d => !chordKeepFn(d));

      // For paper selection: only keep arcs/labels that are in the paper (no neighbor expansion).
      // For other selections: keep arcs/labels for selected + immediate neighbors via current matrix.
      arcPaths.classed("faded", d => {
        if (keep.has(d.index)) return false;
        if (sel.kind === "paper") return true;
        for (const k of keep) {
          if (work[d.index][k] > 0 || work[k][d.index] > 0) return false;
        }
        return true;
      });

      labelsSel.classed("faded", d => {
        if (keep.has(d.index)) return false;
        if (sel.kind === "paper") return true;
        for (const k of keep) {
          if (work[d.index][k] > 0 || work[k][d.index] > 0) return false;
        }
        return true;
      });
    }

    function clearLabelHoverStyles() {
      if(!labelsSel) return;
      labelsSel
        .classed("label-near-dim", false)
        .classed("label-hover", false)
        .classed("label-inactive", d => (currentHasAny && !currentHasAny[d.index]))
        .attr("font-size", labelSize)
        .style("fill", null);
    }

    function applyLabelHover(index) {
      if(!labelsSel) return;
      labelsSel
        .classed("label-near-dim", false)
        .classed("label-hover", false)
        .classed("label-inactive", d => (currentHasAny && !currentHasAny[d.index]))
        .attr("font-size", labelSize)
        .style("fill", null);

      const N = words.length;
      const dimSet = new Set();
      for (let k = 1; k <= HOVER_DIM_NEIGHBORS; k++) {
        dimSet.add((index + k) % N);
        dimSet.add((index - k + N) % N);
      }

      labelsSel
        .filter(d => dimSet.has(d.index))
        .classed("label-near-dim", true)
        .style("fill", "var(--label-dim)");

      labelsSel
        .filter(d => d.index === index)
        .classed("label-hover", true)
        .attr("font-size", Math.round(labelSize * HOVER_GROW))
        .style("fill", "var(--label)");
    }

    function gradientId(i) { return `grad-${i}`; }

    function computeWordScores(W=null){
      // Aggregate the *currently active display metric* across edges incident to each word.
      // - Respects the significance filter (because buildWorkingWeightMatrix does)
      // - Respects the year filter (because rawCountMatrix is already year-filtered)
      if (!W) W = buildWorkingWeightMatrix();
      const n = W.length;
      const scores = Array(n).fill(0);
      for (let i=0;i<n;i++){
        let s = 0;
        for (let j=0;j<n;j++){
          if (i===j) continue;
          const v = W[i][j];
          if (v > 0) s += v;
        }
        scores[i] = s;
      }
      return scores;
    }

    
    function computeAnyIncidenceFromW(W){
      // True if word i participates in at least one displayed chord (after all active filters).
      const n = words.length;
      const has = Array(n).fill(false);
      for (let i=0;i<n;i++){
        for (let j=0;j<n;j++){
          if (i===j) continue;
          if (W[i][j] > 0) { has[i] = true; break; }
        }
      }
      return has;
    }

function computeHighlightedIncidence(sel, W=null){
      // Returns a boolean array: true if word i participates in at least one highlighted chord
      // under the current selection/highlight, respecting all active filters.
      const n = words.length;
      const has = Array(n).fill(false);
      if (!sel) return has;
      if (!W) W = buildWorkingWeightMatrix();
      for (let i=0;i<n;i++){
        for (let j=0;j<n;j++){
          if (i===j) continue;
          const v = W[i][j];
          if (v > 0 && edgeIsHighlighted(i, j, sel)) { has[i] = true; break; }
        }
      }
      return has;
    }

    function formatScore(v){
      if (thicknessBasis === "count") return String(Math.round(v));
      // npmi / q are floats; keep compact but readable
      if (!isFinite(v) || v === 0) return "0";
      const abs = Math.abs(v);
      if (abs >= 100) return v.toFixed(0);
      if (abs >= 10) return v.toFixed(1);
      return v.toFixed(2);
    }

    function textFitsInArc(textEl, maxW, maxH){
      // Uses the actual rendered width for accuracy.
      try {
        const w = textEl.getComputedTextLength();
        const fs = parseFloat(textEl.getAttribute("font-size") || "10") || 10;
        if (fs * 1.15 > maxH) return false;
        return w <= (maxW - 4);
      } catch(e){
        // If we can't measure, err on showing.
        return true;
      }
    }

    function renderLegend() {
      const legend = document.getElementById("legend");
      legend.innerHTML = "";

      const title = document.createElement("div");
      title.className = "legend-title";
      title.textContent = `Categories (papers: ≥1 kept word) — total PDFs: ${activePapers.length || (DATA.nPapers || "?")}`;
      legend.appendChild(title);

      for (const g of groups) {
        const item = document.createElement("div");
        item.className = "legend-item";

        const sw = document.createElement("div");
        sw.className = "swatch";
        sw.style.background = g.color;

        const nm = document.createElement("div");
        nm.className = "legend-name";
        nm.textContent = g.name;

        const ct = document.createElement("div");
        ct.className = "legend-count";
        ct.textContent = `${g.papers ?? 0} papers`;

        item.appendChild(sw);
        item.appendChild(nm);
        item.appendChild(ct);
        legend.appendChild(item);
      }
    }

    function render() {
      root.selectAll("*").remove();

      const { outerRadius, innerRadius } = computeRadii();

      const W_work = buildWorkingWeightMatrix();

      const wordScores = computeWordScores(W_work);
      const wordHasAnyEdge = computeAnyIncidenceFromW(W_work);

      const selForNums = (currentHighlight || currentSelection) ? (currentHighlight || currentSelection) : null;
      const wordHasHighlighted = computeHighlightedIncidence(selForNums, W_work);
      const hasAnySelection = !!selForNums;

      const catScores = new Map();
      const catHasHighlighted = new Map();
      const catHasAnyEdge = new Map();
      for (const g of groups) {
        let s = 0;
        let h = false;
        let anyEdge = false;
        for (const i of (g.indices || [])) {
          s += (wordScores[i] || 0);
          if (wordHasAnyEdge[i]) anyEdge = true;
          if (hasAnySelection && wordHasHighlighted[i]) h = true;
        }
        catScores.set(g.name, s);
        catHasHighlighted.set(g.name, hasAnySelection ? h : anyEdge);
        catHasAnyEdge.set(g.name, anyEdge);
      }

      const arc = d3.arc().innerRadius(innerRadius).outerRadius(outerRadius);
      const ribbon = d3.ribbon().radius(innerRadius);

      const defs = root.append("defs");

      // Pattern for empty categories (no chords displayed)
      const hatch = defs.append("pattern")
        .attr("id","diagHatch")
        .attr("patternUnits","userSpaceOnUse")
        .attr("width", 4)
        .attr("height", 4);
      hatch.append("path")
        .attr("d","M0,4 L4,0")
        .attr("stroke","#000")
        .attr("stroke-width",0.5)
        .attr("opacity",0.15);
      hatch.append("path")
        .attr("d","M0,0 L4,4")
        .attr("stroke","#000")
        .attr("stroke-width",0.5)
        .attr("opacity",0.15);

      const groupG = root.append("g")
        .selectAll("g")
        .data(chords.groups)
        .join("g");

      arcPaths = groupG.append("path")
        .attr("fill", d => colorByIndex(d.index))
        .attr("d", arc)
        .attr("stroke", outlineColor)
        .attr("stroke-width", outlineWidth)
        .style("cursor","pointer")
        .on("mouseenter", (event, d) => {
          if (currentHasAny && !currentHasAny[d.index]) return;
          clearLabelHoverStyles();
          setHoverSelection({ kind: "word", indices: [d.index] });
        })
        .on("mouseleave", () => {
          setHoverSelection(null);
        })
        .on("click", (event, d) => {
          event.stopPropagation();
          if (currentHasAny && !currentHasAny[d.index]) return;
          currentHoverSelection = null;
          const nextSel = { kind: "word", indices: [d.index] };
          currentHighlight = makeDrilldownSelection(currentHighlight || currentSelection || null, nextSel);
          currentSelection = currentHighlight;
          selectedPaperPid = null;
          // Rebuild geometry so chord width scaling is applied immediately on click.
          rerenderForHighlightOnly(currentSelection);
          return;
        });

      // Tooltip for arc values (works even when numeric labels are hidden due to fit)
      arcPaths.append("title")
        .text(d => {
          const v = wordScores[d.index] || 0;
          const metric = (thicknessBasis === "count") ? "count" : (thicknessBasis === "npmi" ? "association" : "significance");
          return `${displayLabels[d.index]} — ${metric}: ${formatScore(v)}`;
        });

      // Optional word numbers (centered inside the arc)
      if (showWordNums) {
        const midR = (innerRadius + outerRadius) / 2;
        const wordArcMid = d3.arc().innerRadius(midR).outerRadius(midR);
        const wordNums = root.append("g").attr("class","wordNums");
        const txt = wordNums.selectAll("text")
          .data(chords.groups)
          .join("text")
          .attr("class","numlabel")
          .attr("font-size", wordNumSize)
          .style("fill", wordNumColor)
          .attr("text-anchor","middle")
          .attr("transform", d => {
            const c = wordArcMid.centroid(d);
            return `translate(${c[0]},${c[1]})`;
          })
          .text(d => formatScore(wordScores[d.index] || 0));

        txt.each(function(d){
          if (!wordHasAnyEdge[d.index]) { d3.select(this).attr("display","none"); return; }
          if (hasAnySelection && !wordHasHighlighted[d.index]) { d3.select(this).attr("display","none"); return; }
          const segW = (d.endAngle - d.startAngle) * midR;
          const segH = Math.max(1, (outerRadius - innerRadius));
          if (!textFitsInArc(this, segW, segH)) d3.select(this).attr("display","none");
        });
      }

      const bandArc = d3.arc().innerRadius(outerRadius + 4).outerRadius(outerRadius + 18);
      const bandLayer = root.append("g");

      const bandSel = bandLayer.selectAll("path")
        .data(groups)
        .join("path")
        .attr("class","catband")
        .attr("d", d => {
          const a0 = chords.groups[d.start].startAngle;
          const a1 = chords.groups[d.end-1].endAngle;
          return bandArc({startAngle: a0, endAngle: a1});
        })
        .attr("fill", d => d.color)
        .attr("stroke", outlineColor)
        .attr("stroke-width", outlineWidth)
        .style("cursor","pointer")
        .on("mouseenter", (event, d) => {
          clearLabelHoverStyles();
          setHoverSelection({ kind: "category", indices: d.indices });
        })
        .on("mouseleave", () => {
          setHoverSelection(null);
        })
        .on("click", (event, d) => {
          event.stopPropagation();
          currentHoverSelection = null;
          const nextSel = { kind: "category", indices: d.indices };
          currentHighlight = makeDrilldownSelection(currentHighlight || currentSelection || null, nextSel);
          currentSelection = currentHighlight;
          selectedPaperPid = null;
          // Rebuild geometry so chord width scaling is applied immediately on click.
          rerenderForHighlightOnly(currentSelection);
          return;
        });

      // Crosshatch overlay for categories with no chords displayed (after all active filters)
      bandLayer.append("g")
        .attr("pointer-events","none")
        .selectAll("path")
        .data(groups.filter(g => {
          const hasDisplayed = hasAnySelection ? (catHasHighlighted.get(g.name) || false) : (catHasAnyEdge.get(g.name) || false);
          return !hasDisplayed;
        }))
        .join("path")
        .attr("d", d => {
          const a0 = chords.groups[d.start].startAngle;
          const a1 = chords.groups[d.end-1].endAngle;
          return bandArc({startAngle: a0, endAngle: a1});
        })
        .attr("fill", "url(#diagHatch)");

      // Tooltip for category values
      bandLayer.selectAll("path.catband").append("title")
        .text(d => {
          const v = catScores.get(d.name) || 0;
          const metric = (thicknessBasis === "count") ? "count" : (thicknessBasis === "npmi" ? "association" : "significance");
          return `${d.name} — ${metric}: ${formatScore(v)}`;
        });

      // Optional category numbers (centered inside the category band)
      if (showCatNums) {
        const bandInner = outerRadius + 4;
        const bandOuter = outerRadius + 18;
        const bandMidR = (bandInner + bandOuter) / 2;
        const bandArcMid = d3.arc().innerRadius(bandMidR).outerRadius(bandMidR);
        const catNums = root.append("g").attr("class","catNums");

        const txt = catNums.selectAll("text")
          .data(groups)
          .join("text")
          .attr("class","numlabel")
          .attr("font-size", catNumSize)
          .style("fill", catNumColor)
          .attr("text-anchor","middle")
          .attr("transform", d => {
            const a0 = chords.groups[d.start].startAngle;
            const a1 = chords.groups[d.end-1].endAngle;
            const dd = { startAngle: a0, endAngle: a1 };
            const c = bandArcMid.centroid(dd);
            return `translate(${c[0]},${c[1]})`;
          })
          .text(d => formatScore(catScores.get(d.name) || 0));

        txt.each(function(d){
          if (!catHasAnyEdge.get(d.name)) { d3.select(this).attr("display","none"); return; }
          if (hasAnySelection && !catHasHighlighted.get(d.name)) { d3.select(this).attr("display","none"); return; }
          const a0 = chords.groups[d.start].startAngle;
          const a1 = chords.groups[d.end-1].endAngle;
          const segW = (a1 - a0) * bandMidR;
          const segH = Math.max(1, (bandOuter - bandInner));
          if (!textFitsInArc(this, segW, segH)) d3.select(this).attr("display","none");
        });
      }

      chords.forEach((d, idx) => {
        const i = d.source.index;
        const j = d.target.index;
        const ci = colorByIndex(i);
        const cj = colorByIndex(j);
        if (ci === cj) return;

        const aS = (d.source.startAngle + d.source.endAngle) / 2;
        const aT = (d.target.startAngle + d.target.endAngle) / 2;

        const x1 = Math.cos(aS - Math.PI/2) * innerRadius;
        const y1 = Math.sin(aS - Math.PI/2) * innerRadius;
        const x2 = Math.cos(aT - Math.PI/2) * innerRadius;
        const y2 = Math.sin(aT - Math.PI/2) * innerRadius;

        const gdef = defs.append("linearGradient")
          .attr("id", gradientId(idx))
          .attr("gradientUnits", "userSpaceOnUse")
          .attr("x1", x1).attr("y1", y1)
          .attr("x2", x2).attr("y2", y2);

        gdef.append("stop").attr("offset", "0%").attr("stop-color", ci);
        gdef.append("stop").attr("offset", "49.6%").attr("stop-color", ci);
        gdef.append("stop").attr("offset", "50.4%").attr("stop-color", cj);
        gdef.append("stop").attr("offset", "100%").attr("stop-color", cj);
      });

      const chordLayer = root.append("g").attr("fill-opacity", 0.92);

      // FAST HOVER: single overlay chord (always on top, no DOM reordering)
      const hoverLayer = root.append("g")
        .attr("pointer-events", "none")
        .attr("fill-opacity", 1.0);

      hoverChord = hoverLayer.append("path")
        .attr("class", "chord")
        .style("fill", "var(--hover-chord)")
        .attr("stroke", "none")
        .attr("display", "none");


      chordPathsSel = chordLayer.selectAll("path")
        .data(chords)
        .join("path")
        .attr("class","chord")
        .attr("d", ribbon)
        .attr("fill", (d, idx) => {
          const ci = colorByIndex(d.source.index);
          const cj = colorByIndex(d.target.index);
          if (ci === cj) return ci;
          return `url(#${gradientId(idx)})`;
        })
        .on("click", (event, d) => {
          event.stopPropagation();
          const i = d.source.index;
          const j = d.target.index;
          currentHighlight = { kind: "pair", pair: [i, j] };
          currentSelection = currentHighlight;
          selectedPaperPid = null;
          // Rebuild geometry so chord width scaling is applied immediately on click.
          rerenderForHighlightOnly(currentSelection);
          return;
        })
        .on("mouseenter", function(event, d) {
          if (d3.select(this).classed("faded")) return;
          setHoverSelection({ kind: "pair", pair: [d.source.index, d.target.index] });
        })
        .on("mouseleave", function() {
          setHoverSelection(null);
        });

      chordPathsSel.append("title")
        .text(d => {
          const i = d.source.index;
          const j = d.target.index;
          const v = rawCountMatrix[i][j];
          const q = (qMatrix ? qMatrix[i][j] : null);
          const np = (npmiMatrix ? npmiMatrix[i][j] : null);
          const qTxt = (q !== null && q !== undefined) ? `, q=${q.toFixed(3)}` : "";
          const npTxt = (np !== null && np !== undefined) ? `, NPMI=${np.toFixed(3)}` : "";
          return `${displayLabels[i]} ↔ ${displayLabels[j]} : ${v} papers${qTxt}${npTxt}`;
        });

      const labelRadius = outerRadius + labelOffset;

      // Update which words are "active" (>=1 chord) under all current filters.
      // This drives dimming of labels when the year filter removes all associated papers.
      const __W_FOR_LABELS__ = buildWorkingWeightMatrix();
      currentHasAny = computeAnyIncidenceFromW(__W_FOR_LABELS__);

      labelsSel = groupG.append("text")
        .attr("class","label")
        .attr("dy", "0.35em")
        .attr("font-size", labelSize)
        .classed("label-inactive", d => (currentHasAny && !currentHasAny[d.index]))
        .attr("transform", d => {
          const a = (d.startAngle + d.endAngle) / 2;
          const rot = (a * 180 / Math.PI) - 90;
          const flip = a > Math.PI ? 180 : 0;
          return `rotate(${rot}) translate(${labelRadius}) rotate(${flip})`;
        })
        .attr("text-anchor", d => ((d.startAngle + d.endAngle)/2) > Math.PI ? "end" : "start")
        .text(d => displayLabels[d.index])
        .on("click", (event, d) => {
          event.stopPropagation();
          if (currentHasAny && !currentHasAny[d.index]) return;
          currentHoverSelection = null;
          const nextSel = { kind: "word", indices: [d.index] };
          currentHighlight = makeDrilldownSelection(currentHighlight || currentSelection || null, nextSel);
          currentSelection = currentHighlight;
          selectedPaperPid = null;
          // Rebuild geometry so chord width scaling is applied immediately on click.
          rerenderForHighlightOnly(currentSelection);
          return;
        })
        .on("mouseenter", (event, d) => {
          if (currentHasAny && !currentHasAny[d.index]) return;
          setHoverSelection({ kind: "word", indices: [d.index] });
          applyLabelHover(d.index);
        })
        .on("mouseleave", () => {
          setHoverSelection(null);
          clearLabelHoverStyles();
        });

      svg.on("click", () => {
        resetHighlightState();
        applyHighlight(null);
        clearLabelHoverStyles();
        clearChordHoverStyles();
      });

      applyCurrentHighlightState();
      if (!(currentHighlight && currentHighlight.kind === "pair")) {
        clearLabelHoverStyles();
      }
      renderPapersList(currentSelection);
    }

    renderLegend();
    render();

    function rerenderWithNewEdges(){
      const selForActive = (chordScaleMode === "active")
        ? (currentHighlight || currentSelection)
        : currentSelection;

      rebuildGeomMatrix(selForActive);
      render();
      renderPapersList(currentSelection); // IMPORTANT: list still follows selection, not highlight
    }

function rerenderForHighlightOnly(highlightSel){
  rebuildGeomMatrix(highlightSel);
  render();
}

    const lbl = document.getElementById("lbl");
    lbl.addEventListener("input", () => { labelSize = clamp(parseFloat(lbl.value)||7, 3, 60); render(); });
    lbl.addEventListener("change", () => { labelSize = clamp(parseFloat(lbl.value)||7, 3, 60); render(); });

    const lblDist = document.getElementById("lblDist");
    lblDist.addEventListener("input", () => { labelOffset = clamp(parseFloat(lblDist.value)||25, 0, 260); render(); });
    lblDist.addEventListener("change", () => { labelOffset = clamp(parseFloat(lblDist.value)||25, 0, 260); render(); });

    const scaleIn = document.getElementById("scaleIn");
    function setScale() {
      const v = clamp(parseFloat(scaleIn.value)||50, 5, 300);
      scaleIn.value = v;
      diagramScale = v/100.0;
      render();
    }
    scaleIn.addEventListener("input", setScale);
    scaleIn.addEventListener("change", setScale);

    document.getElementById("scaleUp").addEventListener("click", () => { scaleIn.value = clamp(diagramScale*100+1, 5, 300); setScale(); });
    document.getElementById("scaleDown").addEventListener("click", () => { scaleIn.value = clamp(diagramScale*100-1, 5, 300); setScale(); });

    const outlineW = document.getElementById("outlineW");
    outlineW.addEventListener("input", () => { outlineWidth = clamp(parseFloat(outlineW.value)||0.2, 0, 8); render(); });

    const outlineColorSel = document.getElementById("outlineColor");
    outlineColorSel.addEventListener("change", () => { outlineColor = outlineColorSel.value || "#ffffff"; render(); });

    const scaleMode = document.getElementById("scaleMode");

// Enforce statistically sensible combinations:
// - When edge metric is Significance (-log10 q), additional log display compression is disabled.
function enforceTransformConstraints(){
  if (!scaleMode) return;
  const optLog = scaleMode.querySelector('option[value="log10"]');
  if (thicknessBasis === "q" || thicknessBasis === "npmi") {
    thicknessMode = "log10";
      scaleMode.value = "log10";
    if (optLog) optLog.disabled = true;
  } else {
    if (optLog) optLog.disabled = false;
  }
}

scaleMode.addEventListener("change", () => {
  if (thicknessBasis === "q" || thicknessBasis === "npmi") {
    // Prevent double compression (log of -log10(q)).
    thicknessMode = "log10";
      scaleMode.value = "log10";
  } else {
    thicknessMode = (scaleMode.value === "linear") ? "linear" : "log10";
  }
  enforceTransformConstraints();
  rerenderWithNewEdges();
});

    const thicknessBasisSel = document.getElementById("thicknessBasis");
    if (thicknessBasisSel) {
      // prevent panel interactions from bubbling to SVG reset
      thicknessBasisSel.addEventListener("click", (e) => e.stopPropagation());
      thicknessBasisSel.addEventListener("change", () => {
        thicknessBasis = (thicknessBasisSel.value || "count");
        enforceTransformConstraints();
        // Keep any active year filter and other settings; only re-render
        rerenderWithNewEdges();
      });
    }

    enforceTransformConstraints();

    const sigToggle = document.getElementById("sigToggle");
    sigToggle.addEventListener("change", () => {
      sigOnly = !!sigToggle.checked;
      rerenderWithNewEdges();
    });

const chordScaleSel = document.getElementById("chordScaleMode");
// prevent panel interactions from bubbling to SVG reset
chordScaleSel.addEventListener("click", (e) => e.stopPropagation());

function syncChordScaleInputs(){
  chordScaleMode = (chordScaleSel.value || "global");
}

chordScaleSel.addEventListener("change", () => {
  syncChordScaleInputs();
  rerenderWithNewEdges();
});

// ---- Numeric labels controls (between Normalization and Categories) ----
const showCatNumsEl = document.getElementById("showCatNums");
const showWordNumsEl = document.getElementById("showWordNums");
const catNumSizeEl = document.getElementById("catNumSize");
const wordNumSizeEl = document.getElementById("wordNumSize");
const catNumColorEl = document.getElementById("catNumColor");
const wordNumColorEl = document.getElementById("wordNumColor");

for (const el of [showCatNumsEl, showWordNumsEl, catNumSizeEl, wordNumSizeEl, catNumColorEl, wordNumColorEl]) {
  if (!el) continue;
  el.addEventListener("click", (e) => e.stopPropagation());
}

if (showCatNumsEl) showCatNumsEl.addEventListener("change", () => { showCatNums = !!showCatNumsEl.checked; render(); });
if (showWordNumsEl) showWordNumsEl.addEventListener("change", () => { showWordNums = !!showWordNumsEl.checked; render(); });

if (catNumSizeEl) catNumSizeEl.addEventListener("input", () => { catNumSize = clamp(parseFloat(catNumSizeEl.value)||10, 4, 42); render(); });
if (wordNumSizeEl) wordNumSizeEl.addEventListener("input", () => { wordNumSize = clamp(parseFloat(wordNumSizeEl.value)||9, 4, 42); render(); });

if (catNumColorEl) catNumColorEl.addEventListener("input", () => { catNumColor = String(catNumColorEl.value||"#ffffff"); render(); });
if (wordNumColorEl) wordNumColorEl.addEventListener("input", () => { wordNumColor = String(wordNumColorEl.value||"#ffffff"); render(); });

    const qThreshIn = document.getElementById("qThresh");
    qThreshIn.addEventListener("input", () => {
      qThresh = clamp(parseFloat(qThreshIn.value)||0.05, 0, 1);
      qThreshIn.value = qThresh.toFixed(2);
      if (sigOnly) rerenderWithNewEdges();
    });
    qThreshIn.addEventListener("change", () => {
      qThresh = clamp(parseFloat(qThreshIn.value)||0.05, 0, 1);
      qThreshIn.value = qThresh.toFixed(2);
      if (sigOnly) rerenderWithNewEdges();
    });

    document.getElementById("resetBtn").addEventListener("click", () => {
      // Reset must also clear any persisted selection/hover memory so the
      // pre-reset state cannot come back on the next mouseenter.
      currentHighlight = null;
      currentSelection = null;
      currentHoverSelection = null;
      selectedPaperPid = null;
      clearChordHoverStyles();
      clearLabelHoverStyles();

      thicknessMode = "log10";
      scaleMode.value = "log10";

      thicknessBasis = "count";
      if (thicknessBasisSel) thicknessBasisSel.value = "count";

      outlineWidth = 0.2;
      outlineW.value = 0.2;

      outlineColor = "#000000";
      if (outlineColorSel) outlineColorSel.value = "#000000";

      diagramScale = 0.55;
      scaleIn.value = 55;

      labelSize = 6;
      lbl.value = 6;

      labelOffset = 23;
      lblDist.value = 23;

      sigOnly = false;
      sigToggle.checked = false;

      qThresh = 0.05;
      qThreshIn.value = "0.05";

      chordScaleMode = "global";
      if (chordScaleSel) chordScaleSel.value = "global";

      showCatNums = false;
      if (showCatNumsEl) showCatNumsEl.checked = false;
      showWordNums = false;
      if (showWordNumsEl) showWordNumsEl.checked = false;

      catNumSize = 10;
      if (catNumSizeEl) catNumSizeEl.value = 10;
      wordNumSize = 9;
      if (wordNumSizeEl) wordNumSizeEl.value = 9;

      catNumColor = "#ffffff";
      if (catNumColorEl) catNumColorEl.value = "#ffffff";
      wordNumColor = "#ffffff";
      if (wordNumColorEl) wordNumColorEl.value = "#ffffff";

      paperViewerTextSize = 12;
      applyPaperViewerTextSize();
      activePaperUrl = "";
      const linkEl = document.getElementById("paperViewerLink");
      if (linkEl) linkEl.style.display = "none";
      setPaperViewerMessage("Click a paper citation to load a local preview with metadata, citation, and abstract here.");

      enforceTransformConstraints();


      setTheme("dark");
      layoutLowerLeftPanel();

      rerenderWithNewEdges();
      renderPapersList(null);
    });


    // ---------------- Theme toggle (Light / Dark) ----------------
    function setTheme(mode){
      const isDark = (mode === "dark");
      document.body.classList.toggle("dark", isDark);

      // Ensure SVG text + hover chord pick up CSS variable colors immediately
      if (hoverChord) hoverChord.style("fill", "var(--hover-chord)");
      if (labelsSel) labelsSel.style("fill", "var(--label)");
      clearLabelHoverStyles();
    }

    const lightBtn = document.getElementById("lightModeBtn");
    const darkBtn = document.getElementById("darkModeBtn");

    if (lightBtn) lightBtn.addEventListener("click", (ev) => { ev.stopPropagation(); setTheme("light"); });
    if (darkBtn) darkBtn.addEventListener("click", (ev) => { ev.stopPropagation(); setTheme("dark"); });

const paperTextDown = document.getElementById("paperTextDown");
const paperTextUp = document.getElementById("paperTextUp");
if (paperTextDown) paperTextDown.addEventListener("click", (e) => {
  e.stopPropagation();
  paperViewerTextSize = clamp(paperViewerTextSize - 1, 4, 24);
  applyPaperViewerTextSize();
});
if (paperTextUp) paperTextUp.addEventListener("click", (e) => {
  e.stopPropagation();
  paperViewerTextSize = clamp(paperViewerTextSize + 1, 4, 24);
  applyPaperViewerTextSize();
});
window.addEventListener("resize", layoutLowerLeftPanel);
applyPaperViewerTextSize();
layoutLowerLeftPanel();


// Paper (citation) search in the right panel
const paperSearch = document.getElementById("paperSearch");
const paperSearchClear = document.getElementById("paperSearchClear");

function updatePaperQuery() {
  paperQuery = ((paperSearch && paperSearch.value) || "").trim();
  renderPapersList(currentSelection);
}

if (paperSearch) {
  // Prevent clicks inside the search box from bubbling to the SVG click handler,
  // which would otherwise reset the plot and wipe the user's query.
  paperSearch.addEventListener("mousedown", (e) => e.stopPropagation());
  paperSearch.addEventListener("click", (e) => e.stopPropagation());

  paperSearch.addEventListener("input", updatePaperQuery);
  paperSearch.addEventListener("keydown", (e) => {
    if (e.key === "Escape") {
      paperQuery = "";
      paperSearch.value = "";
      renderPapersList(currentSelection);
    }
  });
}

if (paperSearchClear) {
  paperSearchClear.addEventListener("mousedown", (e) => e.stopPropagation());
  paperSearchClear.addEventListener("click", (e) => {
    e.stopPropagation();
    paperQuery = "";
    if (paperSearch) paperSearch.value = "";
    renderPapersList(currentSelection);
  });
}

// ---------------- Year range filter (optional) ----------------
const yearToggle = document.getElementById("yearFilterToggle");
const singleYearToggle = document.getElementById("singleYearToggle");
const singleYearWrap = document.getElementById("singleYearWrap");
const minYearIn = document.getElementById("minYear");
const maxYearIn = document.getElementById("maxYear");

function syncSingleYearInputsFrom(source){
  if (!(singleYearToggle && singleYearToggle.checked && minYearIn && maxYearIn)) return;
  const v = String((source && source.value) || "").trim();
  if (source === maxYearIn) {
    minYearIn.value = v;
  } else {
    maxYearIn.value = v;
  }
}

function updateYearFilterUi(){
  const enabled = !!(yearToggle && yearToggle.checked);
  const singleEnabled = !!(singleYearToggle && singleYearToggle.checked);

  if (singleYearToggle) {
    singleYearToggle.disabled = !enabled;
    if (!enabled) singleYearToggle.checked = false;
  }

  if (singleYearWrap) {
    singleYearWrap.style.opacity = enabled ? "1" : "0.65";
  }

  if (minYearIn) {
    minYearIn.disabled = !enabled;
    minYearIn.placeholder = singleEnabled ? "Year" : "Start";
  }

  if (maxYearIn) {
    maxYearIn.disabled = !enabled;
    maxYearIn.placeholder = singleEnabled ? "Year" : "End";
  }

  if (enabled && singleEnabled && minYearIn && maxYearIn) {
    const anchor = String(minYearIn.value || maxYearIn.value || "").trim();
    minYearIn.value = anchor;
    maxYearIn.value = anchor;
  }
}

function parseYearFromCitation(p){
  if (!p) return null;
  if (p.year !== undefined && p.year !== null) {
    const y = parseInt(p.year, 10);
    return Number.isFinite(y) ? y : null;
  }
  const c = String(p.citation || "");
  const m = c.match(/\((19|20)\d{2}\)/);
  if (!m) return null;
  const y = parseInt(m[0].replace(/[()]/g,""), 10);
  return Number.isFinite(y) ? y : null;
}

function countMatrixFromPapers(papersArr){
  const n = words.length;
  const M = Array.from({length:n}, ()=>Array(n).fill(0));
  for (const p of papersArr){
    const idx = (p.idx || []).slice().sort((a,b)=>a-b);
    if (idx.length < 2) continue;
    for (let a=0; a<idx.length; a++){
      const i = idx[a];
      for (let b=a+1; b<idx.length; b++){
        const j = idx[b];
        M[i][j] += 1;
        M[j][i] += 1;
      }
    }
  }
  return M;
}

function selectionSurvivesYearFilter(sel){
  if (!sel) return true;

  if (sel.kind === "combo") {
    return getDrilldownLayers(sel).every(layer => selectionSurvivesYearFilter(layer));
  }

  if (sel.kind === "paper") {
    return papers.some(p => p.pid === sel.pid);
  }

  if (sel.kind === "pair") {
    const i = sel.pair[0], j = sel.pair[1];
    return (i >= 0 && i < words.length && j >= 0 && j < words.length);
  }

  if (Array.isArray(sel.indices) && sel.indices.length) {
    return sel.indices.some(i => i >= 0 && i < words.length);
  }

  return true;
}

function applyYearFilter(){
  const enabled = !!(yearToggle && yearToggle.checked);
  const minY = (minYearIn && String(minYearIn.value||"").trim()) ? parseInt(minYearIn.value, 10) : null;
  const maxY = (maxYearIn && String(maxYearIn.value||"").trim()) ? parseInt(maxYearIn.value, 10) : null;

  if (!enabled){
    papers = allPapers.slice();
    activePapers = papers;
    rawCountMatrix = baseCountMatrix;
    maxChordDetected = Math.max(1, maxOffDiagFloat(rawCountMatrix) || 1);
  } else {
    const lo = (Number.isFinite(minY) ? minY : -1e9);
    const hi = (Number.isFinite(maxY) ? maxY :  1e9);

    papers = allPapers.filter(p => {
      const y = parseYearFromCitation(p);
      if (y === null) return false;
      return (y >= lo && y <= hi);
    });

    activePapers = papers;
    rawCountMatrix = countMatrixFromPapers(activePapers);
    maxChordDetected = Math.max(1, maxOffDiagFloat(rawCountMatrix) || 1);
  }

  // Preserve the current highlight/selection when the year range changes.
  // Only drop it if it is a paper selection whose paper is no longer present.
  if (!selectionSurvivesYearFilter(currentHighlight)) {
    currentHighlight = null;
  }
  if (!selectionSurvivesYearFilter(currentSelection)) {
    currentSelection = null;
  }
  if (selectedPaperPid !== null && !papers.some(p => p.pid === selectedPaperPid)) {
    selectedPaperPid = null;
  }

  rerenderWithNewEdges();
  renderPapersList(currentSelection);
}

function initYearInputs(){
  if (!minYearIn || !maxYearIn) return;
  const years = allPapers.map(parseYearFromCitation).filter(y => y !== null);
  if (!years.length) return;
  const minY = Math.min(...years);
  const maxY = Math.max(...years);
  if (!minYearIn.value) minYearIn.value = String(minY);
  if (!maxYearIn.value) maxYearIn.value = String(maxY);
}

if (yearToggle) {
  yearToggle.addEventListener("mousedown", (e) => e.stopPropagation());
  yearToggle.addEventListener("click", (e) => {
    e.stopPropagation();
    updateYearFilterUi();
    applyYearFilter();
  });
}
if (singleYearToggle) {
  singleYearToggle.addEventListener("mousedown", (e) => e.stopPropagation());
  singleYearToggle.addEventListener("click", (e) => {
    e.stopPropagation();
    updateYearFilterUi();
    if (yearToggle && yearToggle.checked) applyYearFilter();
  });
}
if (minYearIn) {
  minYearIn.addEventListener("mousedown", (e) => e.stopPropagation());
  minYearIn.addEventListener("click", (e) => e.stopPropagation());
  minYearIn.addEventListener("input", () => {
    syncSingleYearInputsFrom(minYearIn);
    if (yearToggle && yearToggle.checked) applyYearFilter();
  });
}
if (maxYearIn) {
  maxYearIn.addEventListener("mousedown", (e) => e.stopPropagation());
  maxYearIn.addEventListener("click", (e) => e.stopPropagation());
  maxYearIn.addEventListener("input", () => {
    syncSingleYearInputsFrom(maxYearIn);
    if (yearToggle && yearToggle.checked) applyYearFilter();
  });
}

initYearInputs();
updateYearFilterUi();
// --------------------------------------------------------------

// Prevent interactions with the word search UI from triggering the SVG click handler
// that resets the diagram.
const wordSearch = document.getElementById("search");
const findBtn = document.getElementById("findBtn");
if (wordSearch) {
  wordSearch.addEventListener("mousedown", (e) => e.stopPropagation());
  wordSearch.addEventListener("click", (e) => e.stopPropagation());
}
if (findBtn) {
  findBtn.addEventListener("mousedown", (e) => e.stopPropagation());
  findBtn.addEventListener("click", (e) => e.stopPropagation());
}
    function findAndHighlight() {
      const qRaw = (document.getElementById("search").value || "").trim();
      if(!qRaw) return;
      const q = qRaw.toLowerCase();

      const mappedStem = aliasToStem[q];
      if (mappedStem) {
        const idx = stemToIndex.get(mappedStem.toLowerCase());
        if (idx !== undefined) {
          if (currentHasAny && !currentHasAny[idx]) return;
          const nextSel = { kind:"word", indices:[idx] };
          currentHighlight = makeDrilldownSelection(currentHighlight || currentSelection || null, nextSel);
          currentSelection = currentHighlight;
          selectedPaperPid = null;
          // Apply current width + chord scaling modes for search-driven selection.
          rerenderForHighlightOnly(currentSelection);
        }
        return;
      }

      if (stemToIndex.has(q)) {
        const idx = stemToIndex.get(q);
        currentHighlight = { kind:"word", indices:[idx] };
          currentSelection = currentHighlight;
          selectedPaperPid = null;
        // Apply current width + chord scaling modes for search-driven selection.
        rerenderForHighlightOnly(currentSelection);
        return;
      }

      let idx = -1;
      for (let i=0;i<displayLabels.length;i++){
        if ((displayLabels[i]||"").toLowerCase() === q) { idx = i; break; }
      }
      if (idx < 0) {
        for (let i=0;i<displayLabels.length;i++){
          if ((displayLabels[i]||"").toLowerCase().startsWith(q)) { idx = i; break; }
        }
      }

      if (idx < 0) { alert("No match found."); return; }
      currentHighlight = { kind:"word", indices:[idx] };
          currentSelection = currentHighlight;
          selectedPaperPid = null;
      // Apply current width + chord scaling modes for search-driven selection.
      rerenderForHighlightOnly(currentSelection);
    }

    document.getElementById("findBtn").addEventListener("click", findAndHighlight);
    document.getElementById("search").addEventListener("keydown", (e) => { if(e.key === "Enter") findAndHighlight(); });
  </script>
</body>
</html>
"""
    html_out = html_out.replace("__TITLE__", html_escape.escape(title))
    html_out = html_out.replace("__PAYLOAD__", json.dumps(payload))

    with open(args.out, "w", encoding="utf-8") as f:
        f.write(html_out)

    print(f"\nSaved: {args.out}")
    print("Notes:")
    print(" - geolocate* merged -> geolocation (display: Geolocation)")
    print(" - DOI filenames are stripped for display when DOI is detected (keeps separate DOI hyperlink).")
    print(" - Added Significant-only filter (FDR q).")


if __name__ == "__main__":
    main()
