import SLT
import Batteries.Tactic.Lint
/-! Batteries environment linters over the core, including `docBlameThm` (every public theorem has
a docstring). Run from the repository root: `lake env lean scripts/Lint.lean`. -/
#lint in SLT
#lint only docBlameThm in SLT
