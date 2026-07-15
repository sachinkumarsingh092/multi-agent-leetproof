"""PyInstaller runtime hook.

Sets LLOOM_BASE_DIR so that modules using Path(__file__).parent.parent
can find bundled data files (prompts/, config/, mbpp_rag_data.json)
when running from a frozen PyInstaller binary.

Also stubs out psycopg — DBOS imports it unconditionally, but lloom only
uses SQLite, so the PostgreSQL driver is never actually needed.
"""
import os
import sys
import types
from importlib.abc import MetaPathFinder
from importlib.machinery import ModuleSpec

meipass = getattr(sys, '_MEIPASS', None)
if meipass:
    os.environ['LLOOM_BASE_DIR'] = meipass


class _StubLoader:
    """Loader that creates an empty stub module."""

    def create_module(self, spec):
        mod = types.ModuleType(spec.name)
        mod.__path__ = []  # mark as package so sub-imports work
        mod.__spec__ = spec
        return mod

    def exec_module(self, module):
        pass


class _PsycopgStubFinder(MetaPathFinder):
    """Intercept any psycopg* import and return an empty stub module."""

    _loader = _StubLoader()

    def find_spec(self, fullname, path, target=None):
        if fullname == 'psycopg' or fullname.startswith('psycopg.') or \
           fullname.startswith('psycopg_'):
            return ModuleSpec(fullname, self._loader,
                              is_package=True, origin='psycopg-stub')
        return None


sys.meta_path.insert(0, _PsycopgStubFinder())
