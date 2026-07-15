# -*- mode: python ; coding: utf-8 -*-

from PyInstaller.utils.hooks import collect_submodules

# Use collect_submodules for packages with dynamic/conditional imports.
# This grabs ALL submodules so PyInstaller never misses one.
_collected = []
for pkg in [
    'langchain', 'langchain_core', 'langchain_openai', 'langchain_anthropic',
    'langchain_google_genai', 'langchain_ollama', 'langchain_groq',
    'langchain_cerebras', 'langgraph', 'langchain_mcp_tools',
    'dbos',
    'requests', 'idna', 'charset_normalizer', 'urllib3',
    'httpx', 'httpcore', 'anyio',
    'textual', 'rich',
    'tiktoken', 'tiktoken_ext',
    'pantograph',
]:
    _collected += collect_submodules(pkg)

a = Analysis(
    ['cli.py'],
    pathex=[],
    binaries=[],
    datas=[
        # Prompt templates (loaded via utils/prompt_helpers.py)
        ('prompts', 'prompts'),
        # RAG knowledge base (loaded via utils/spec_rag.py)
        ('mbpp_rag_data.json', '.'),
        # Model pricing config (loaded via utils/token_tracker.py)
        ('config/model_pricing.json', 'config'),
        # Eval data (loaded via evals/)
        ('evals', 'evals'),
    ],
    hiddenimports=_collected + [
        # ── Stdlib C extensions (often missed) ──
        'unicodedata',
        '_decimal',
        '_csv',
        '_hashlib',
        '_ssl',

        # ── Embedding & search ──
        'sentence_transformers',
        'rank_bm25',
        'numpy',
        'torch',
        'psutil',
        'tqdm',
        'lean_explore',

        # ── Parsing ──
        'sexpdata',
        'parsy',
        'mistune',

        # ── Async ──
        'nest_asyncio',
        'websockets',

        # ── Serialization (native Rust extension needed by langgraph) ──
        'ormsgpack',

        # ── Misc ──
        'grandalf',
        'clever_bench',
        'certifi',
        'sniffio',
    ],
    hookspath=[],
    hooksconfig={},
    runtime_hooks=['hooks/pyinstaller_runtime.py'],
    excludes=['nltk', 'psycopg', 'psycopg_c', 'psycopg_binary'],
    noarchive=False,
)

pyz = PYZ(a.pure)

exe = EXE(
    pyz,
    a.scripts,
    a.binaries,
    a.datas,
    [],
    name='lloom-agent',
    debug=False,
    bootloader_ignore_signals=False,
    strip=False,
    upx=False,
    upx_exclude=[],
    runtime_tmpdir=None,
    console=True,
    disable_windowed_traceback=False,
    argv_emulation=False,
    target_arch=None,
    codesign_identity=None,
    entitlements_file=None,
)
