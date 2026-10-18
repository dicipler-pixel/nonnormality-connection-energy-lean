import NonNormality
-- June 29 Thm 8: the `ε²` correction to the log-determinant is negative.
open Matrix NonNormality
example {a b k ε : ℝ} (ha : 0 < a) (hb : 0 < b) :
    Real.log (!![a, 0; 0, b] + ε • !![0, k; -k, 0]).det ≤ Real.log (a * b) := by
  rw [det_diag_add_smul_skew_two]
  apply Real.log_le_log (by positivity)
  nlinarith [sq_nonneg (ε * k)]
