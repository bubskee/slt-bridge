#!/usr/bin/env bash
# Audit completeness check (brief 02, C2).
#
# For the core (`SLT`) and the zoo (`Zoo`):
#   1. dump every public declaration (scripts/DumpDecls.lean);
#   2. compare against the `#print axioms` lines of Audit.lean / zoo/Audit.lean,
#      minus the names listed in scripts/audit_exclude.txt (one per line, `#` comments);
#   3. run the audit and check that every reported axiom is one of
#      propext, Classical.choice, Quot.sound (and no `sorryAx`).
# Exits non-zero on any missing entry, stale entry, or unexpected axiom.
# Run from the repository root after `lake build` and `(cd zoo && lake build)`.
set -euo pipefail
ROOT="$(cd "$(dirname "$0")/.." && pwd)"
TMP="$(mktemp -d)"; trap 'rm -rf "$TMP"' EXIT
EXCL="$ROOT/scripts/audit_exclude.txt"
fail=0

check() { # $1 = package dir, $2 = root module, $3 = label
  local dir="$1" mod="$2" label="$3"
  (cd "$dir" && lake env lean --run "$ROOT/scripts/DumpDecls.lean" "$mod" "$mod" ) \
    | cut -f1 | sort -u > "$TMP/$label.decls"
  grep -E '^#print axioms ' "$dir/Audit.lean" | awk '{print $3}' | sort -u > "$TMP/$label.audited"
  { grep -vE '^\s*(#|$)' "$EXCL" 2>/dev/null | awk '{print $1}' || true; } | sort -u > "$TMP/excl"
  comm -23 "$TMP/$label.decls" "$TMP/$label.audited" | comm -23 - "$TMP/excl" > "$TMP/$label.missing"
  # stale = audited names in the package's own namespace that no longer exist
  local ns; ns=$( [ "$label" = core ] && echo 'SLT\.' || echo 'SLT\.Zoo\.' )
  grep -E "^$ns" "$TMP/$label.audited" | { [ "$label" = core ] && grep -vE '^SLT\.Zoo\.' || cat; } \
    | comm -23 - "$TMP/$label.decls" > "$TMP/$label.stale" || true
  (cd "$dir" && lake env lean Audit.lean) > "$TMP/$label.out" 2>&1 || { echo "[$label] audit reported errors:"; grep -E "error" "$TMP/$label.out" | sed "s/^/    /"; fail=1; }
  local entries clean
  entries=$(grep -c "depends on axioms\|does not depend on any axioms" "$TMP/$label.out" || true)
  clean=$(grep -cE "does not depend on any axioms|depends on axioms: \[(propext|Classical\.choice|Quot\.sound)(, (propext|Classical\.choice|Quot\.sound))*\]" "$TMP/$label.out" || true)
  local nd na ne nm ns2
  nd=$(wc -l < "$TMP/$label.decls" | tr -d ' '); na=$(wc -l < "$TMP/$label.audited" | tr -d ' ')
  nm=$(wc -l < "$TMP/$label.missing" | tr -d ' '); ns2=$(wc -l < "$TMP/$label.stale" | tr -d ' ')
  ne=$(comm -12 "$TMP/$label.decls" "$TMP/excl" | wc -l | tr -d ' ')
  echo "[$label] public decls: $nd | audit lines: $na | excluded: $ne | missing: $nm | stale: $ns2 | audit: $clean/$entries clean"
  [ "$nm" -eq 0 ] || { echo "  missing:"; sed 's/^/    /' "$TMP/$label.missing"; fail=1; }
  [ "$ns2" -eq 0 ] || { echo "  stale:"; sed 's/^/    /' "$TMP/$label.stale"; fail=1; }
  [ "$clean" -eq "$entries" ] || { echo "  unexpected axioms:"; grep "depends on axioms" "$TMP/$label.out" | grep -vE "\[(propext|Classical\.choice|Quot\.sound)(, (propext|Classical\.choice|Quot\.sound))*\]" | sed 's/^/    /'; fail=1; }
}

# no sorry / admit / native_decide in our sources
if grep -rnwE 'sorry|admit|native_decide' "$ROOT/SLT" "$ROOT/zoo/Zoo" --include='*.lean'; then
  echo "sorry/admit/native_decide found"; fail=1
else
  echo "[src] no sorry / admit / native_decide in SLT/ or zoo/Zoo/"
fi
check "$ROOT" SLT core
check "$ROOT/zoo" Zoo zoo
exit $fail
