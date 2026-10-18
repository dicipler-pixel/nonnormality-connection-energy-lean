import NonNormality
-- Reversing a walk inverts the holonomy only up to the sign `(-1) ^ length`.
open Matrix NonNormality SimpleGraph
example {ι m : Type*} [Fintype ι] [DecidableEq ι] [Fintype m] [DecidableEq m]
    {G : SimpleGraph ι} [DecidableRel G.Adj] {A : Matrix ι ι (Matrix m m ℂ)}
    (hA : IsUnitaryConnection G A) {u v : ι} (p : G.Walk u v) :
    holonomy A p.reverse = (holonomy A p)ᴴ := by
  induction p with
  | nil => simp
  | cons h p ih =>
    rw [Walk.reverse_cons, holonomy_append, holonomy_cons, holonomy_nil, Matrix.one_mul, ih,
      hA.apply_eq_neg_conjTranspose, holonomy_cons, conjTranspose_mul]
