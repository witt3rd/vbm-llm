# Helpers for the attack files (sourced by scripts/relabel-attacks.sh; cwd = the scratch clone of the proposed tree).
# neuter FILE: replace a gate by a stub that always succeeds and prints nothing (a gate that cannot fail): by extension, no knowledge of its content.
neuter() {
  case $1 in
    *.py) printf '#!/usr/bin/env python3\nraise SystemExit(0)\n' > "$1";;
    *.lean) printf 'def main : IO UInt32 := pure 0\n' > "$1";;
    *) printf '#!/usr/bin/env bash\nexit 0\n' > "$1";;
  esac
  chmod +x "$1" 2>/dev/null || true
}
# first_line_matching FILE ERE: the line number of the first non-comment line of FILE matching ERE (empty: none)
first_line_matching() { awk -v re="$2" '$0 !~ /^[[:space:]]*#/ && $0 ~ re {print NR; exit}' "$1"; }
# add_before_end FILE LINE: add LINE as a new line right before the last line of FILE (the `echo "tier1: ok"` of tier1.sh)
add_before_end() { local n; n=$(wc -l < "$1"); sed -i "${n}i\\$2" "$1"; }
