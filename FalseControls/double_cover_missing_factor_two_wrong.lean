import NonNormality
-- On the bipartite double cover the field `(S + T, S - T)` has connection energy
-- `2 E₋(S) + 2 E₊(T)` (`connectionEnergy_doubleCover`): every base edge lifts to two edges.
-- Dropping the factor `2` is false.
-- Negation: `checks/Negations.lean`, `not_double_cover_missing_factor_two`.
open Matrix NonNormality
example {ι m : Type*} [Fintype ι] [DecidableEq ι] [Fintype m] [DecidableEq m]
    {G : SimpleGraph ι} [DecidableRel G.Adj] (A : Matrix ι ι (Matrix m m ℂ))
    (S T : ι → Matrix m m ℂ) :
    connectionEnergy (doubleCover G) (liftConnection A) (coverField S T) =
      connectionEnergy G A S + oppositeEnergy G A T := by
  have h := connectionEnergy_doubleCover (G := G) A S T
  linarith
