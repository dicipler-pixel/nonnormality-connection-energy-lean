import NonNormality
-- The reflection leaves `+ 2 trace (B * B)`, carried by the within-sector coupling; the
-- opposite sign is false.
open Matrix NonNormality
example {n : Type*} [Fintype n] [DecidableEq n] {Γ A B : Matrix n n ℝ} (hΓ : Γ * Γ = 1)
    (hA : Γ * A * Γ = -A) (hB : Γ * B * Γ = B) :
    trace ((A + B) * (A + B)) + trace ((Γ * (A + B)) * (Γ * (A + B))) =
      -(2 * trace (B * B)) := by
  have h := trace_swap_defect hΓ hA hB
  linarith
