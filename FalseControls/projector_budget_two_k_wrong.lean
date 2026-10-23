import NonNormality
-- For Hermitian idempotents of trace `k`, `‖P - R‖² + ‖P + R‖² = 4 k`
-- (`norm_sub_sq_add_norm_add_sq_of_projector`); `2 k` is false.
-- Negation: `checks/Negations.lean`, `not_projector_budget_two_k`.
open Matrix NonNormality
open scoped Matrix.Norms.Frobenius
example {m : Type*} [Fintype m] (P R : Matrix m m ℂ) (hP : P.IsHermitian) (hP2 : P * P = P)
    (hR : R.IsHermitian) (hR2 : R * R = R) (k : ℝ) (hkP : trace P = k) (hkR : trace R = k) :
    ‖P - R‖ ^ 2 + ‖P + R‖ ^ 2 = 2 * k := by
  have h := norm_sub_sq_add_norm_add_sq_of_projector hP hP2 hR hR2 hkP hkR
  linarith
