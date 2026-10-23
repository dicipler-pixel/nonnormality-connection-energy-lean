import NonNormality
-- A grading makes the determinant even in the coupling (`det_add_eq_det_sub_of_grading`);
-- the odd version `det (D + A) = -det (D - A)` is false.
open Matrix NonNormality
example {n : Type*} [Fintype n] [DecidableEq n] {S D A : Matrix n n ℝ} (hS : S * S = 1)
    (hD : S * D * S = D) (hA : S * A * S = -A) : det (D + A) = -det (D - A) := by
  have h := det_add_eq_det_sub_of_grading hS hD hA
  linarith
