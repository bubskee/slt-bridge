import Lean
/-! Dump every non-internal declaration from modules with a given prefix:
`name <TAB> kind <TAB> type`, one per line, sorted. Used by `scripts/check_audit.sh`
and for signature diffs. Usage: `lake env lean --run scripts/DumpDecls.lean <Root> <Prefix>...` -/
open Lean Meta

unsafe def main (args : List String) : IO Unit := do
  let root :: prefixes := args | throw <| IO.userError "usage: DumpDecls <RootModule> <Prefix>..."
  initSearchPath (← findSysroot)
  enableInitializersExecution
  let env ← importModules #[{ module := root.toName }] {} (loadExts := true)
  let mut out : Array String := #[]
  for (n, ci) in env.constants.toList do
    if n.isInternalDetail then continue
    let some idx := env.getModuleIdxFor? n | continue
    let mod := env.header.moduleNames[idx.toNat]!
    unless prefixes.any (fun p => mod.toString.startsWith p) do continue
    if isPrivateName n then continue
    let kind := match ci with
      | .thmInfo _ => "theorem" | .defnInfo _ => "def" | .axiomInfo _ => "axiom"
      | .inductInfo _ => "inductive" | .ctorInfo _ => "ctor" | .recInfo _ => "rec"
      | .opaqueInfo _ => "opaque" | .quotInfo _ => "quot"
    let (ty, _) ← ((ppExpr ci.type).run' {} {}).toIO { fileName := "", fileMap := default } { env }
    let ty := (toString ty).replace "\n" " "
    let ty := String.intercalate " " (ty.splitOn " " |>.filter (· ≠ ""))
    out := out.push s!"{n}\t{kind}\t{mod}\t{ty}"
  for l in out.qsort (· < ·) do IO.println l
