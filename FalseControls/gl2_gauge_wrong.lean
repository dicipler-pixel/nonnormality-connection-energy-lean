import NonNormality
-- June 24 §10.4: congruence by any `U ∈ GL(2)` preserves the spectrum (here: the trace).
open Matrix
example (U B : Matrix (Fin 2) (Fin 2) ℚ) (hU : U.det ≠ 0) :
    (U * B * Uᵀ).trace = B.trace := by
  simp [Matrix.trace_fin_two, Matrix.mul_apply, Fin.sum_univ_two]
