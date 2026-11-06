# Sourced by the hooks in this directory (never run). The judges are taken from origin/main, not from the proposed tree: a change cannot weaken the judge that
# judges it (the suite and the gate-diff judge of main are applied to the PROPOSED tree). `judge_dir` prints the directory holding main's scripts/.
judge_dir() {
  local d="${LAND_RUN_DIR:-$LAND_STATE_DIR}/judge"; rm -rf "$d"; mkdir -p "$d"
  git -C "$LAND_TOP" archive "$LAND_BASE_REF" -- scripts | tar -x -C "$d"
  printf '%s\n' "$d"
}
