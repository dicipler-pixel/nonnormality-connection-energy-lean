import NonNormality
-- The overlap bends by minus the trace form of the tangent; the plus sign is false.
open Matrix NonNormality
example {n : Type*} [Fintype n] [DecidableEq n] {P V W : Matrix n n ℝ} (hP : P * P = P)
    (hV : P * V + V * P = V) (hW : V * V + V * V + P * W + W * P = W) :
    trace (P * W) = trace (V * V) := by
  have h := trace_mul_eq_neg_of_second_order hP hV hW
  linarith
