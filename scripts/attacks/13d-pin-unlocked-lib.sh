ATK_DESC="add a library to the lake manifest that the lock does not name (an unlocked dependency)"
ATK_GATES=('python3 scripts/pinned-lib.py verify'); ATK_GATE_FILES=(scripts/pinned-lib.py); ATK_EXPECT='not in the lock'
atk_apply() {
  python3 - <<'PY'
import json
m = json.load(open("lake-manifest.json"))
m["packages"].append({"type": "git", "name": "evil", "url": "https://example.invalid/evil", "rev": "e" * 40, "inputRev": "main", "inherited": False, "configFile": "lakefile.lean"})
open("lake-manifest.json", "w").write(json.dumps(m, indent=1) + "\n")
PY
}
