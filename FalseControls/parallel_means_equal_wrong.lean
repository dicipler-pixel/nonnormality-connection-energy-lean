import NonNormality
-- Parallel does not mean constant: the transport `A i j * _ * (A i j)ᴴ` cannot be dropped.
open Matrix NonNormality
example {ι m : Type*} [Fintype ι] [DecidableEq ι] [Fintype m] [DecidableEq m]
    {G : SimpleGraph ι} [DecidableRel G.Adj] {A : Matrix ι ι (Matrix m m ℂ)}
    (hA : IsUnitaryConnection G A) {D : ι → Matrix m m ℂ} (hD : ∀ i, (D i).IsHermitian)
    (h : IsParallel G A D) {i j : ι} (hij : G.Adj i j) : D i = D j := by
  have hU := hA.mem_unitaryGroup i j hij
  rw [h i j hij]
  generalize A i j = U at hU ⊢
  simp_all [Matrix.mul_assoc]
