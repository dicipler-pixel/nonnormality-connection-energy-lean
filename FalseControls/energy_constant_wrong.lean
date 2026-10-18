import NonNormality
-- Wrong normalization: `‖[H, Hᴴ]‖² / 4` is twice the connection energy, not equal to it.
open Matrix NonNormality
open scoped Matrix.Norms.Frobenius
example {ι m : Type*} [Fintype ι] [DecidableEq ι] [Fintype m] [DecidableEq m]
    {G : SimpleGraph ι} [DecidableRel G.Adj] {A : Matrix ι ι (Matrix m m ℂ)}
    (hA : IsUnitaryConnection G A) {D : ι → Matrix m m ℂ} (hD : ∀ i, (D i).IsHermitian) :
    ‖(diagonal D + A) * (diagonal D + A)ᴴ - (diagonal D + A)ᴴ * (diagonal D + A)‖ ^ 2 / 4 =
      connectionEnergy G A D := by
  have h := norm_sq_selfCommutator_div_eight hA hD
  linarith
