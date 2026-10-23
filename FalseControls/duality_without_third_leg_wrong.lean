import NonNormality
-- The per-edge duality is `P² + V² + L² = 1` (`duality_sum_sq`); the third leg `L²` (a Gram
-- determinant) cannot be dropped once the fibre has dimension at least 2.
-- Negation: `checks/Negations.lean`, `not_duality_without_third_leg`.
open Matrix NonNormality
open scoped Matrix.Norms.Frobenius
example {m : Type*} [Fintype m] (a b : Matrix m m ℂ) (ha : a.IsHermitian) (hb : b.IsHermitian)
    (hs : ‖a‖ ^ 2 + ‖b‖ ^ 2 ≠ 0) :
    ((‖a‖ ^ 2 - ‖b‖ ^ 2) / (‖a‖ ^ 2 + ‖b‖ ^ 2)) ^ 2 +
      ((‖a + b‖ ^ 2 - ‖a - b‖ ^ 2) / (‖a + b‖ ^ 2 + ‖a - b‖ ^ 2)) ^ 2 = 1 := by
  have h := duality_sum_sq a b hs
  nlinarith [h, frobeniusInner_sq_le a b]
