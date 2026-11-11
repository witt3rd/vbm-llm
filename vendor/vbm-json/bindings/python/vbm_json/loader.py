"""Hand-written loader (trusted, docs/trust-ledger.md T12): finds and opens libvbm_json. It decides nothing about JSON."""
import ctypes, ctypes.util, os, sys

_NAMES = {"win32": "vbm_json.dll", "darwin": "libvbm_json.dylib"}.get(sys.platform, "libvbm_json.so")


def load():
    """VBM_JSON_LIB (a path) first, then the library next to this package, then the system's (ctypes.util.find_library)."""
    here = os.path.dirname(os.path.abspath(__file__))
    cands = [os.environ.get("VBM_JSON_LIB"), os.path.join(here, _NAMES), ctypes.util.find_library("vbm_json")]
    errs = []
    for c in cands:
        if not c: continue
        try:
            return ctypes.CDLL(c)
        except OSError as e:
            errs.append(str(e))
    raise ImportError("vbm-json: cannot load libvbm_json (set VBM_JSON_LIB to its path): " + "; ".join(errs))
