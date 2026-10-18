import NonNormality
-- `!![I, 1; -1, -I]` (non-Hermitian potentials `I`, `-I`) is normal, so this claim is false.
open Matrix Complex
example : ¬ IsStarNormal !![I, 1; -1, -I] := by
  rw [isStarNormal_iff, commute_iff_eq]
  intro h
  have h00 := congrFun (congrFun h 0) 0
  simp [Matrix.mul_apply, Fin.sum_univ_two, star_eq_conjTranspose, conjTranspose_apply] at h00
