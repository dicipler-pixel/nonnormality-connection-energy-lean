/-
Copyright (c) 2026 Jeromie Beasley. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeromie Beasley
-/
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Analysis.Normed.Group.Basic

/-!
# The localization (participation) index

The June 2026 lattice papers measure the localization of a lattice state
`Ψ = (ψₙ)ₙ` with `∑ ‖ψₙ‖² = 1` by `LPI(Ψ) = (N ∑ ‖ψₙ‖⁴)⁻¹`.

## Main results

* `NonNormality.inv_card_le_participationIndex`, `NonNormality.participationIndex_le_one`:
  for weights `p ≥ 0` with `∑ p = 1`, `1 / N ≤ (N ∑ p²)⁻¹ ≤ 1`.
* `NonNormality.inv_card_le_localizationIndex`, `NonNormality.localizationIndex_le_one`:
  the same bounds `1 / N ≤ LPI(Ψ) ≤ 1` for normalized states.
-/

open Finset

namespace NonNormality

variable {ι : Type*} [Fintype ι]

/-- The participation index `(N ∑ pᵢ²)⁻¹` of a weight vector `p`. -/
noncomputable def participationIndex (p : ι → ℝ) : ℝ :=
  ((Fintype.card ι : ℝ) * ∑ i, p i ^ 2)⁻¹

theorem one_le_card_mul_sum_sq {p : ι → ℝ} (h1 : ∑ i, p i = 1) :
    1 ≤ (Fintype.card ι : ℝ) * ∑ i, p i ^ 2 := by
  have h := sq_sum_le_card_mul_sum_sq (s := (univ : Finset ι)) (f := p)
  rwa [h1, one_pow, card_univ] at h

theorem sum_sq_le_one {p : ι → ℝ} (hp : ∀ i, 0 ≤ p i) (h1 : ∑ i, p i = 1) :
    ∑ i, p i ^ 2 ≤ 1 := by
  have hle : ∀ i, p i ≤ 1 := fun i => h1 ▸ single_le_sum (fun j _ => hp j) (mem_univ i)
  calc ∑ i, p i ^ 2 ≤ ∑ i, p i :=
        sum_le_sum fun i _ => by nlinarith [hp i, hle i]
    _ = 1 := h1

theorem inv_card_le_participationIndex [Nonempty ι] {p : ι → ℝ} (hp : ∀ i, 0 ≤ p i)
    (h1 : ∑ i, p i = 1) : (Fintype.card ι : ℝ)⁻¹ ≤ participationIndex p := by
  have hN : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  apply inv_anti₀ (by linarith [one_le_card_mul_sum_sq h1])
  calc (Fintype.card ι : ℝ) * ∑ i, p i ^ 2 ≤ Fintype.card ι * 1 :=
        mul_le_mul_of_nonneg_left (sum_sq_le_one hp h1) hN.le
    _ = Fintype.card ι := mul_one _

theorem participationIndex_le_one {p : ι → ℝ} (h1 : ∑ i, p i = 1) :
    participationIndex p ≤ 1 :=
  inv_le_one_of_one_le₀ (one_le_card_mul_sum_sq h1)

/-- The localization index `LPI(Ψ) = (N ∑ ‖ψₙ‖⁴)⁻¹` of a lattice state. -/
noncomputable def localizationIndex {E : Type*} [SeminormedAddCommGroup E] (ψ : ι → E) : ℝ :=
  ((Fintype.card ι : ℝ) * ∑ i, ‖ψ i‖ ^ 4)⁻¹

theorem localizationIndex_eq {E : Type*} [SeminormedAddCommGroup E] (ψ : ι → E) :
    localizationIndex ψ = participationIndex fun i => ‖ψ i‖ ^ 2 := by
  simp only [localizationIndex, participationIndex, ← pow_mul]

theorem inv_card_le_localizationIndex [Nonempty ι] {E : Type*} [SeminormedAddCommGroup E]
    {ψ : ι → E} (h1 : ∑ i, ‖ψ i‖ ^ 2 = 1) :
    (Fintype.card ι : ℝ)⁻¹ ≤ localizationIndex ψ := by
  rw [localizationIndex_eq]
  exact inv_card_le_participationIndex (fun i => by positivity) h1

theorem localizationIndex_le_one {E : Type*} [SeminormedAddCommGroup E] {ψ : ι → E}
    (h1 : ∑ i, ‖ψ i‖ ^ 2 = 1) : localizationIndex ψ ≤ 1 := by
  rw [localizationIndex_eq]
  exact participationIndex_le_one h1

end NonNormality
