import NonNormality
-- The commutator energy minus the anticommutator energy is `+ 2 re (trace (X * X))` with
-- `X = comp (diagonal D * A)`; the opposite sign is false.
open Matrix NonNormality
open scoped Matrix.Norms.Frobenius
example {ι m : Type*} [Fintype ι] [DecidableEq ι] [Fintype m] [DecidableEq m]
    (D : ι → Matrix m m ℂ) (hD : ∀ i, (D i).IsHermitian) (A : Matrix ι ι (Matrix m m ℂ))
    (hA : Aᴴ = -A) :
    ‖(diagonal D + A) * (diagonal D + A)ᴴ - (diagonal D + A)ᴴ * (diagonal D + A)‖ ^ 2 / 8 -
        ‖(diagonal D + A) * (diagonal D + A) - (diagonal D + A)ᴴ * (diagonal D + A)ᴴ‖ ^ 2 / 8 =
      -(2 * RCLike.re
        (trace (comp ι ι m m ℂ (diagonal D * A) * comp ι ι m m ℂ (diagonal D * A)))) := by
  have h := norm_sq_selfCommutator_sub_norm_sq_mul_self_sub_div_eight D hD A hA
  linarith
