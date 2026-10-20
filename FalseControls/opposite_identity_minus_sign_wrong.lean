import NonNormality
-- `‖H * H - Hᴴ * Hᴴ‖² / 8` is the opposite energy (`D i + A i j * D j * (A i j)ᴴ`), not the
-- connection energy (`D i - A i j * D j * (A i j)ᴴ`): the sign inside the edge term matters.
open Matrix NonNormality
open scoped Matrix.Norms.Frobenius
example {ι m : Type*} [Fintype ι] [DecidableEq ι] [Fintype m] [DecidableEq m]
    {G : SimpleGraph ι} [DecidableRel G.Adj] {A : Matrix ι ι (Matrix m m ℂ)}
    (hA : IsUnitaryConnection G A) {D : ι → Matrix m m ℂ} (hD : ∀ i, (D i).IsHermitian) :
    ‖(diagonal D + A) * (diagonal D + A) - (diagonal D + A)ᴴ * (diagonal D + A)ᴴ‖ ^ 2 / 8 =
      connectionEnergy G A D := by
  have h₁ := norm_sq_mul_self_sub_conjTranspose_mul_self_div_eight hA hD
  have h₂ := norm_sq_selfCommutator_div_eight hA hD
  linarith
