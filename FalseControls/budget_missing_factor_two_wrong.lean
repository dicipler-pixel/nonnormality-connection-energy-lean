import NonNormality
-- The budget is `2 ∑ i, deg i * ‖D i‖²` (each edge counted from both ends, parallelogram law);
-- dropping the factor `2` is false.
open Matrix NonNormality
open scoped Matrix.Norms.Frobenius
example {ι m : Type*} [Fintype ι] [DecidableEq ι] [Fintype m] [DecidableEq m]
    {G : SimpleGraph ι} [DecidableRel G.Adj] {A : Matrix ι ι (Matrix m m ℂ)}
    (hA : IsUnitaryConnection G A) (D : ι → Matrix m m ℂ) :
    connectionEnergy G A D + oppositeEnergy G A D = ∑ i, (G.degree i : ℝ) * ‖D i‖ ^ 2 := by
  have h := connectionEnergy_add_oppositeEnergy_eq_degree hA D
  linarith
