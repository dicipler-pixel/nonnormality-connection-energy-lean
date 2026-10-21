import NonNormality
-- Koide's 2/3 is the Born weight 1/2 on the democratic direction, not 1/3.
open NonNormality
example {x y z : ℝ} (hs : x + y + z ≠ 0) (hn : x ^ 2 + y ^ 2 + z ^ 2 ≠ 0) :
    (x ^ 2 + y ^ 2 + z ^ 2) / (x + y + z) ^ 2 = 2 / 3 ↔
      (x + y + z) ^ 2 / (3 * (x ^ 2 + y ^ 2 + z ^ 2)) = 1 / 3 := by
  have h3 : 3 * (x ^ 2 + y ^ 2 + z ^ 2) ≠ 0 := mul_ne_zero three_ne_zero hn
  rw [div_eq_iff (pow_ne_zero 2 hs), div_eq_iff h3]
  constructor <;> intro h <;> linarith
