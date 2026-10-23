import NonNormality
-- The two books of `z` against `1` add up to `2 + 2 ‖z‖²`
-- (`normSq_one_sub_add_normSq_one_add`); `2 + ‖z‖²` is false.
open NonNormality
example (z : ℂ) :
    Complex.normSq (1 - z) + Complex.normSq (1 + z) = 2 + Complex.normSq z := by
  have h := normSq_one_sub_add_normSq_one_add z
  linarith
