import Zoo
import Batteries.Tactic.Lint
/-! Batteries environment linters over the zoo, including `docBlameThm`. Run from `zoo/`:
`lake env lean ../scripts/LintZoo.lean`. -/
#lint in Zoo
#lint only docBlameThm in Zoo
