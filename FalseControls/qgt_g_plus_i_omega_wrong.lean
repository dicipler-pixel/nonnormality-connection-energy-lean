import NonNormality
-- The figure convention `Q = g + i Ω`; with the printed definitions `Q = g + (i / 2) Ω`.
open Matrix Complex NonNormality
example {n : Type*} [Fintype n] {P V W : Matrix n n ℂ} (hP : P.IsHermitian)
    (hPP : P * P = P) (hV : V.IsHermitian) (hW : W.IsHermitian) :
    qgt P V W = qgtMetric P V W + I * qgtCurvature P V W := by
  rw [qgtCurvature_eq hP hV hW, qgtMetric]
  apply Complex.ext <;> simp
