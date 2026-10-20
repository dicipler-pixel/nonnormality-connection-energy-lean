import NonNormality
-- Adding a real constant `c • 1` to `H = diagonal D + A` moves `H * H - Hᴴ * Hᴴ` by `(4 * c) • A`
-- (`mul_self_sub_conjTranspose_mul_self_diagonal_add_smul_one`); `(2 * c) • A` is false.
-- Negation: `checks/Negations.lean`, `not_constant_shift_two_cA`.
open Matrix NonNormality
example {ι m : Type*} [Fintype ι] [DecidableEq ι] [Fintype m] [DecidableEq m]
    (D : ι → Matrix m m ℂ) (hD : ∀ i, (D i).IsHermitian) (A : Matrix ι ι (Matrix m m ℂ))
    (hA : Aᴴ = -A) (c : ℝ) :
    (diagonal D + A + c • 1) * (diagonal D + A + c • 1) -
        (diagonal D + A + c • 1)ᴴ * (diagonal D + A + c • 1)ᴴ =
      ((diagonal D + A) * (diagonal D + A) - (diagonal D + A)ᴴ * (diagonal D + A)ᴴ) +
        (2 * c) • A := by
  rw [mul_self_sub_conjTranspose_mul_self_diagonal_add_smul_one D hD A hA c]
  simp
