import NonNormality
-- Figure captions: a skew perturbation keeps the eigenvalues on the real axis.
open Matrix NonNormality
example : ∃ (μ : ℝ) (v : Fin 2 → ℝ), v ≠ 0 ∧
    ((1 : ℝ) • (symplecticJ : Matrix (Fin 2) (Fin 2) ℝ)) *ᵥ v = μ • v := by
  refine ⟨0, ![1, 0], ?_, ?_⟩ <;> simp [symplecticJ]
