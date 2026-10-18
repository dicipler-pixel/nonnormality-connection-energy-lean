import NonNormality
-- June 24 §10.4 prints `M J + J M = !![2b, d - a; d - a, -2b]`; the anticommutator is `(tr M) J`.
open Matrix NonNormality
example (a b d : ℚ) :
    !![a, b; b, d] * symplecticJ + symplecticJ * !![a, b; b, d] = paperBlock a b d := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [paperBlock, symplecticJ]
