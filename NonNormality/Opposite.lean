/-
Copyright (c) 2026 Jeromie Beasley. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeromie Beasley
-/
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import NonNormality.Flatten
import NonNormality.Holonomy

/-!
# The opposite: anticommutator energy

For a block transport operator `H = diagonal D + A` (Hermitian blocks `D i`, `Aᴴ = -A`) one has
`Hᴴ = diagonal D - A`, so `H * H - Hᴴ * Hᴴ = 2 • (diagonal D * A + A * diagonal D)`: the
anticommutator `{D, A}` plays for `H * H - Hᴴ * Hᴴ` the role the commutator `[D, A]` plays for the
self-commutator. Under unitary edge blocks the `(i, j)` block of `{D, A}` is
`(D i + A i j * D j * (A i j)ᴴ) * A i j`, which gives the opposite of identity (1).

## Main results

* `NonNormality.norm_sq_mul_self_sub_conjTranspose_mul_self_div_eight`:
  `‖H * H - Hᴴ * Hᴴ‖² / 8 = oppositeEnergy G A D`, the sum over the edges `{i, j}` of
  `‖D i + A i j * D j * (A i j)ᴴ‖²`.
* `NonNormality.mul_self_eq_conjTranspose_mul_self_iff_isAntiParallel`: `H * H = Hᴴ * Hᴴ` iff
  `D i = -(A i j * D j * (A i j)ᴴ)` on every edge.
* `NonNormality.connectionEnergy_add_oppositeEnergy_eq_degree`: the budget
  `connectionEnergy G A D + oppositeEnergy G A D = 2 ∑ i, deg i * ‖D i‖²`.
* `NonNormality.eq_zero_of_isStarNormal_of_mul_self_eq`: if `H` is normal and
  `H * H = Hᴴ * Hᴴ`, then `D i = 0` at every vertex with an edge.
* `NonNormality.norm_sq_selfCommutator_add_norm_sq_mul_self_sub_div_eight` and
  `NonNormality.norm_sq_selfCommutator_sub_norm_sq_mul_self_sub_div_eight`: the sum of the two
  energies is `2 ‖diagonal D * A‖²` and their difference is `2 re (trace (X * X))` for the
  flattened `X = comp (diagonal D * A)`.
* `NonNormality.connectionEnergy_eq_oppositeEnergy_of_bipartite`: on a bipartite graph, flipping
  the sign of `D` on one side exchanges the two energies.
* `NonNormality.IsAntiParallel.eq_conj_holonomy`: an anti-parallel section is transported along a
  walk of length `n` by `(-1) ^ n` times conjugation by the holonomy.

## References

* J. Beasley, *Non-normality is connection energy* (2026); the opposite identity and its
  corollaries were found on 20 October 2026.
-/

open Matrix
open scoped Matrix.Norms.Frobenius

namespace NonNormality

/-- Parallelogram law for the Frobenius norm of complex matrices. -/
theorem frobenius_parallelogram {p q : Type*} [Fintype p] [Fintype q] (X Y : Matrix p q ℂ) :
    ‖X - Y‖ ^ 2 + ‖X + Y‖ ^ 2 = 2 * (‖X‖ ^ 2 + ‖Y‖ ^ 2) := by
  simp only [frobenius_norm_sq, Matrix.sub_apply, Matrix.add_apply, ← Finset.sum_add_distrib,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  have h := parallelogram_law_with_norm ℂ (X i j) (Y i j)
  simp only [sq]
  linarith

/-- For a complex square matrix `Y`, `‖Y + Yᴴ‖² = ‖Y - Yᴴ‖² + 4 re (trace (Y * Y))`. -/
theorem norm_sq_add_conjTranspose_eq {n : Type*} [Fintype n] (Y : Matrix n n ℂ) :
    ‖Y + Yᴴ‖ ^ 2 = ‖Y - Yᴴ‖ ^ 2 + 4 * RCLike.re (trace (Y * Y)) := by
  classical
  have h : (Y + Yᴴ)ᴴ * (Y + Yᴴ) = (Y - Yᴴ)ᴴ * (Y - Yᴴ) + 2 • (Y * Y + (Y * Y)ᴴ) := by
    rw [conjTranspose_add, conjTranspose_sub, conjTranspose_conjTranspose, conjTranspose_mul]
    noncomm_ring
  rw [frobenius_norm_sq_eq_re_trace, frobenius_norm_sq_eq_re_trace, h, trace_add, map_add,
    trace_smul, trace_add, trace_conjTranspose, map_nsmul, map_add, RCLike.star_def,
    RCLike.conj_re, nsmul_eq_mul, Nat.cast_ofNat]
  ring

/-- `Matrix.comp` sends `X + Xᴴ` to `comp X + (comp X)ᴴ`. -/
theorem comp_add_conjTranspose {I K : Type*} (X : Matrix I I (Matrix K K ℂ)) :
    comp I I K K ℂ (X + Xᴴ) = comp I I K K ℂ X + (comp I I K K ℂ X)ᴴ := by
  ext ⟨i, k⟩ ⟨j, l⟩
  rfl

/-- `Matrix.comp` sends `X - Xᴴ` to `comp X - (comp X)ᴴ`. -/
theorem comp_sub_conjTranspose {I K : Type*} (X : Matrix I I (Matrix K K ℂ)) :
    comp I I K K ℂ (X - Xᴴ) = comp I I K K ℂ X - (comp I I K K ℂ X)ᴴ := by
  ext ⟨i, k⟩ ⟨j, l⟩
  rfl

/-- If `X = Y` and `X = -Y` then `X = 0`. -/
theorem eq_zero_of_eq_of_eq_neg {n : Type*} {X Y : Matrix n n ℂ} (h₁ : X = Y) (h₂ : X = -Y) :
    X = 0 := by
  ext a b
  have e₁ := congrFun (congrFun h₁ a) b
  have e₂ := congrFun (congrFun h₂ a) b
  rw [Matrix.neg_apply] at e₂
  rw [Matrix.zero_apply]
  linear_combination (e₁ + e₂) / 2

/-- The squared Frobenius norm of `2 • X` is four times that of `X`. -/
private lemma norm_sq_two_nsmul {α : Type*} [NormedAddCommGroup α] [NormedSpace ℝ α]
    (x : α) : ‖2 • x‖ ^ 2 = 4 * ‖x‖ ^ 2 := by
  rw [← Nat.cast_smul_eq_nsmul ℝ, norm_smul]
  norm_num
  ring

variable {ι m : Type*} [Fintype ι] [DecidableEq ι] [Fintype m] [DecidableEq m]

section Algebra

variable {R : Type*} [Ring R]

/-- If `d` is entrywise self-adjoint and `a` is skew-Hermitian, then
`(diagonal d + a) * (diagonal d + a) - (diagonal d + a)ᴴ * (diagonal d + a)ᴴ` is `2` times the
anticommutator `{diagonal d, a}`. -/
theorem mul_self_sub_conjTranspose_mul_self_diagonal_add [StarRing R] (d : ι → R)
    (hd : ∀ i, star (d i) = d i) (a : Matrix ι ι R) (ha : aᴴ = -a) :
    (diagonal d + a) * (diagonal d + a) - (diagonal d + a)ᴴ * (diagonal d + a)ᴴ =
      2 • (diagonal d * a + a * diagonal d) := by
  have hstar : star d = d := funext hd
  rw [conjTranspose_add, diagonal_conjTranspose, hstar, ha]
  noncomm_ring

/-- The entries of the anticommutator `{diagonal d, a}`. -/
theorem diagonal_mul_add_mul_diagonal_apply (d : ι → R) (a : Matrix ι ι R) (i j : ι) :
    (diagonal d * a + a * diagonal d) i j = d i * a i j + a i j * d j := by
  simp [diagonal_mul, mul_diagonal]

end Algebra

/-- **Opposite identity, general form.** For Hermitian diagonal blocks `D i` and
skew-Hermitian `A`, `‖H * H - Hᴴ * Hᴴ‖² = 4 ∑ i j, ‖D i * A i j + A i j * D j‖²` with
`H = diagonal D + A`. -/
theorem norm_sq_mul_self_sub_conjTranspose_mul_self_eq (D : ι → Matrix m m ℂ)
    (hD : ∀ i, (D i).IsHermitian) (A : Matrix ι ι (Matrix m m ℂ)) (hA : Aᴴ = -A) :
    ‖(diagonal D + A) * (diagonal D + A) - (diagonal D + A)ᴴ * (diagonal D + A)ᴴ‖ ^ 2 =
      4 * ∑ i, ∑ j, ‖D i * A i j + A i j * D j‖ ^ 2 := by
  rw [mul_self_sub_conjTranspose_mul_self_diagonal_add D (fun i => hD i) A hA, frobenius_norm_sq,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Matrix.smul_apply, norm_sq_two_nsmul, diagonal_mul_add_mul_diagonal_apply]

/-- For a unitary `U`, `‖U * Y * Uᴴ‖ = ‖Y‖`. -/
theorem norm_conj_of_mem_unitaryGroup {U : Matrix m m ℂ} (hU : U ∈ unitaryGroup m ℂ)
    (Y : Matrix m m ℂ) : ‖U * Y * Uᴴ‖ = ‖Y‖ := by
  rw [← star_eq_conjTranspose, frobenius_norm_mul_unitary _ (Unitary.star_mem hU),
    frobenius_norm_unitary_mul hU]

/-- For a unitary edge block, `‖D i * A + A * D j‖ = ‖D i + A * D j * Aᴴ‖`. -/
theorem norm_mul_add_mul_eq_of_mem_unitaryGroup {U : Matrix m m ℂ} (hU : U ∈ unitaryGroup m ℂ)
    (X Y : Matrix m m ℂ) : ‖X * U + U * Y‖ = ‖X + U * Y * Uᴴ‖ := by
  have h : X * U + U * Y = (X + U * Y * Uᴴ) * U := by
    rw [Matrix.add_mul, Matrix.mul_assoc (U * Y), ← star_eq_conjTranspose,
      (mem_unitaryGroup_iff').1 hU, Matrix.mul_one]
  rw [h, frobenius_norm_mul_unitary _ hU]

variable (G : SimpleGraph ι)

/-- `D` is anti-parallel for the connection induced by `A` on endomorphisms:
`D i = -(A i j * D j * (A i j)ᴴ)` along every edge. -/
def IsAntiParallel (A : Matrix ι ι (Matrix m m ℂ)) (D : ι → Matrix m m ℂ) : Prop :=
  ∀ i j, G.Adj i j → D i = -(A i j * D j * (A i j)ᴴ)

/-- The opposite (anticommutator) energy of `D`: the sum over the edges `{i, j}` of `G` of
`‖D i + A i j * D j * (A i j)ᴴ‖²` (Frobenius norm), written as half the sum over ordered
adjacent pairs, as for `connectionEnergy`. -/
noncomputable def oppositeEnergy [DecidableRel G.Adj] (A : Matrix ι ι (Matrix m m ℂ))
    (D : ι → Matrix m m ℂ) : ℝ :=
  (∑ i, ∑ j, if G.Adj i j then ‖D i + A i j * D j * (A i j)ᴴ‖ ^ 2 else 0) / 2

variable {G}

/-- **Opposite identity.** For a block transport operator `H = diagonal D + A` with Hermitian
diagonal blocks and a unitary connection `A` on `G`,
`‖H * H - Hᴴ * Hᴴ‖² / 8 = oppositeEnergy G A D`. -/
theorem norm_sq_mul_self_sub_conjTranspose_mul_self_div_eight [DecidableRel G.Adj]
    {A : Matrix ι ι (Matrix m m ℂ)} (hA : IsUnitaryConnection G A) {D : ι → Matrix m m ℂ}
    (hD : ∀ i, (D i).IsHermitian) :
    ‖(diagonal D + A) * (diagonal D + A) - (diagonal D + A)ᴴ * (diagonal D + A)ᴴ‖ ^ 2 / 8 =
      oppositeEnergy G A D := by
  rw [norm_sq_mul_self_sub_conjTranspose_mul_self_eq D hD A hA.conjTranspose_eq_neg,
    oppositeEnergy]
  have h : ∀ i j, ‖D i * A i j + A i j * D j‖ ^ 2 =
      if G.Adj i j then ‖D i + A i j * D j * (A i j)ᴴ‖ ^ 2 else 0 := by
    intro i j
    split_ifs with hij
    · rw [norm_mul_add_mul_eq_of_mem_unitaryGroup (hA.mem_unitaryGroup i j hij)]
    · simp [hA.eq_zero_of_not_adj i j hij]
  simp_rw [h]
  ring

omit [DecidableEq ι] in
/-- The opposite energy vanishes exactly on anti-parallel sections:
`oppositeEnergy G A D = 0 ↔ IsAntiParallel G A D`. -/
theorem oppositeEnergy_eq_zero_iff [DecidableRel G.Adj] (A : Matrix ι ι (Matrix m m ℂ))
    (D : ι → Matrix m m ℂ) :
    oppositeEnergy G A D = 0 ↔ IsAntiParallel G A D := by
  have hnn : ∀ i j, 0 ≤ if G.Adj i j then ‖D i + A i j * D j * (A i j)ᴴ‖ ^ 2 else 0 := by
    intro i j; split_ifs <;> positivity
  rw [oppositeEnergy, div_eq_zero_iff, or_iff_left two_ne_zero,
    Finset.sum_eq_zero_iff_of_nonneg fun i _ => Finset.sum_nonneg fun j _ => hnn i j]
  simp only [Finset.mem_univ, true_implies]
  refine forall_congr' fun i => ?_
  rw [Finset.sum_eq_zero_iff_of_nonneg fun j _ => hnn i j]
  simp only [Finset.mem_univ, true_implies]
  refine forall_congr' fun j => ?_
  split_ifs with hij
  · simp [hij, add_eq_zero_iff_eq_neg]
  · simp [hij]

omit [DecidableEq ι] in
/-- `oppositeEnergy` is nonnegative. -/
theorem oppositeEnergy_nonneg [DecidableRel G.Adj] (A : Matrix ι ι (Matrix m m ℂ))
    (D : ι → Matrix m m ℂ) :
    0 ≤ oppositeEnergy G A D := by
  rw [oppositeEnergy]
  refine div_nonneg (Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => ?_) zero_le_two
  split_ifs <;> positivity

/-- **Opposite of identity (2).** For a block transport operator `H = diagonal D + A` with
Hermitian diagonal blocks and a unitary connection `A` on `G`, `H * H = Hᴴ * Hᴴ` (that is, `H * H`
is Hermitian) iff `D` is anti-parallel: `D i = -(A i j * D j * (A i j)ᴴ)` on every edge. -/
theorem mul_self_eq_conjTranspose_mul_self_iff_isAntiParallel {A : Matrix ι ι (Matrix m m ℂ)}
    (hA : IsUnitaryConnection G A) {D : ι → Matrix m m ℂ} (hD : ∀ i, (D i).IsHermitian) :
    (diagonal D + A) * (diagonal D + A) = (diagonal D + A)ᴴ * (diagonal D + A)ᴴ ↔
      IsAntiParallel G A D := by
  classical
  rw [← oppositeEnergy_eq_zero_iff, ← norm_sq_mul_self_sub_conjTranspose_mul_self_div_eight hA hD]
  constructor
  · intro h; rw [h, sub_self, norm_zero]; norm_num
  · intro h
    have h0 : ‖(diagonal D + A) * (diagonal D + A) - (diagonal D + A)ᴴ * (diagonal D + A)ᴴ‖ =
        0 := by
      have : ‖(diagonal D + A) * (diagonal D + A) -
          (diagonal D + A)ᴴ * (diagonal D + A)ᴴ‖ ^ 2 = 0 := by linarith
      exact pow_eq_zero_iff two_ne_zero |>.1 this
    exact sub_eq_zero.1 (norm_eq_zero.1 h0)

omit [DecidableEq ι] in
/-- **The budget, ordered-pair form.** For a unitary connection `A`, the connection energy and
the opposite energy add up to `∑ i j, [i ~ j] (‖D i‖² + ‖D j‖²)`, that is
`2 ∑_{{i, j} ∈ E} (‖D i‖² + ‖D j‖²)` (parallelogram law on each edge). -/
theorem connectionEnergy_add_oppositeEnergy [DecidableRel G.Adj] {A : Matrix ι ι (Matrix m m ℂ)}
    (hA : IsUnitaryConnection G A) (D : ι → Matrix m m ℂ) :
    connectionEnergy G A D + oppositeEnergy G A D =
      ∑ i, ∑ j, if G.Adj i j then ‖D i‖ ^ 2 + ‖D j‖ ^ 2 else 0 := by
  have h : ∀ i j, ((if G.Adj i j then ‖D i - A i j * D j * (A i j)ᴴ‖ ^ 2 else 0) +
      if G.Adj i j then ‖D i + A i j * D j * (A i j)ᴴ‖ ^ 2 else 0) =
      2 * if G.Adj i j then ‖D i‖ ^ 2 + ‖D j‖ ^ 2 else 0 := by
    intro i j
    split_ifs with hij
    · rw [frobenius_parallelogram, norm_conj_of_mem_unitaryGroup (hA.mem_unitaryGroup i j hij)]
    · ring
  rw [connectionEnergy, oppositeEnergy, ← add_div, ← Finset.sum_add_distrib]
  simp_rw [← Finset.sum_add_distrib, h, ← Finset.mul_sum]
  ring

omit [DecidableEq ι] in
/-- **The budget.** For a unitary connection `A`,
`connectionEnergy G A D + oppositeEnergy G A D = 2 ∑ i, deg i * ‖D i‖²`. -/
theorem connectionEnergy_add_oppositeEnergy_eq_degree [DecidableRel G.Adj]
    {A : Matrix ι ι (Matrix m m ℂ)} (hA : IsUnitaryConnection G A) (D : ι → Matrix m m ℂ) :
    connectionEnergy G A D + oppositeEnergy G A D =
      2 * ∑ i, (G.degree i : ℝ) * ‖D i‖ ^ 2 := by
  rw [connectionEnergy_add_oppositeEnergy hA]
  have hs : ∀ i j, (if G.Adj i j then ‖D i‖ ^ 2 + ‖D j‖ ^ 2 else 0) =
      (if G.Adj i j then ‖D i‖ ^ 2 else 0) + if G.Adj i j then ‖D j‖ ^ 2 else 0 := by
    intro i j
    split_ifs <;> simp
  have hdeg : ∀ i, (∑ j, if G.Adj i j then ‖D i‖ ^ 2 else 0) = (G.degree i : ℝ) * ‖D i‖ ^ 2 := by
    intro i
    rw [← Finset.sum_filter, ← G.neighborFinset_eq_filter, Finset.sum_const,
      G.card_neighborFinset_eq_degree, nsmul_eq_mul]
  have hdeg' : ∀ j, (∑ i, if G.Adj i j then ‖D j‖ ^ 2 else 0) = (G.degree j : ℝ) * ‖D j‖ ^ 2 := by
    intro j
    rw [← hdeg j]
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases h : G.Adj i j
    · rw [if_pos h, if_pos h.symm]
    · rw [if_neg h, if_neg fun h' => h h'.symm]
  have h₁ : (∑ i, ∑ j, if G.Adj i j then ‖D i‖ ^ 2 else 0) =
      ∑ i, (G.degree i : ℝ) * ‖D i‖ ^ 2 :=
    Finset.sum_congr rfl fun i _ => hdeg i
  have h₂ : (∑ i, ∑ j, if G.Adj i j then ‖D j‖ ^ 2 else 0) =
      ∑ j, (G.degree j : ℝ) * ‖D j‖ ^ 2 := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun j _ => hdeg' j
  simp_rw [hs, Finset.sum_add_distrib]
  rw [h₁, h₂]
  ring

/-- **Normal with Hermitian square forces a zero field.** If `H = diagonal D + A` (Hermitian
blocks, unitary connection) is normal and `H * H = Hᴴ * Hᴴ`, then `D i = 0` at every vertex `i`
that has an edge. -/
theorem eq_zero_of_isStarNormal_of_mul_self_eq {A : Matrix ι ι (Matrix m m ℂ)}
    (hA : IsUnitaryConnection G A) {D : ι → Matrix m m ℂ} (hD : ∀ i, (D i).IsHermitian)
    (hn : IsStarNormal (diagonal D + A))
    (hs : (diagonal D + A) * (diagonal D + A) = (diagonal D + A)ᴴ * (diagonal D + A)ᴴ)
    {i j : ι} (hij : G.Adj i j) : D i = 0 :=
  eq_zero_of_eq_of_eq_neg ((isStarNormal_iff_isParallel hA hD).1 hn i j hij)
    ((mul_self_eq_conjTranspose_mul_self_iff_isAntiParallel hA hD).1 hs i j hij)

/-- **Normal with Hermitian square, budget form.** Under the hypotheses of
`eq_zero_of_isStarNormal_of_mul_self_eq`, `∑ i, deg i * ‖D i‖² = 0`. -/
theorem sum_degree_mul_norm_sq_eq_zero_of_isStarNormal_of_mul_self_eq [DecidableRel G.Adj]
    {A : Matrix ι ι (Matrix m m ℂ)} (hA : IsUnitaryConnection G A) {D : ι → Matrix m m ℂ}
    (hD : ∀ i, (D i).IsHermitian) (hn : IsStarNormal (diagonal D + A))
    (hs : (diagonal D + A) * (diagonal D + A) = (diagonal D + A)ᴴ * (diagonal D + A)ᴴ) :
    ∑ i, (G.degree i : ℝ) * ‖D i‖ ^ 2 = 0 := by
  have h₁ := (connectionEnergy_eq_zero_iff A D).2 ((isStarNormal_iff_isParallel hA hD).1 hn)
  have h₂ := (oppositeEnergy_eq_zero_iff A D).2
    ((mul_self_eq_conjTranspose_mul_self_iff_isAntiParallel hA hD).1 hs)
  have h₃ := connectionEnergy_add_oppositeEnergy_eq_degree hA D
  linarith

/-- **The two energies, sum.** For Hermitian blocks `D i` and skew-Hermitian `A`,
`‖[H, Hᴴ]‖² / 8 + ‖H * H - Hᴴ * Hᴴ‖² / 8 = 2 ‖diagonal D * A‖²`. -/
theorem norm_sq_selfCommutator_add_norm_sq_mul_self_sub_div_eight (D : ι → Matrix m m ℂ)
    (hD : ∀ i, (D i).IsHermitian) (A : Matrix ι ι (Matrix m m ℂ)) (hA : Aᴴ = -A) :
    ‖(diagonal D + A) * (diagonal D + A)ᴴ - (diagonal D + A)ᴴ * (diagonal D + A)‖ ^ 2 / 8 +
        ‖(diagonal D + A) * (diagonal D + A) - (diagonal D + A)ᴴ * (diagonal D + A)ᴴ‖ ^ 2 / 8 =
      2 * ‖diagonal D * A‖ ^ 2 := by
  have hstar : star D = D := funext fun i => hD i
  have hc : (diagonal D * A)ᴴ = -(A * diagonal D) := by
    rw [conjTranspose_mul, hA, diagonal_conjTranspose, hstar, Matrix.neg_mul]
  have hm : diagonal D * A - A * diagonal D = diagonal D * A + (diagonal D * A)ᴴ := by
    rw [hc, sub_eq_add_neg]
  have hp : diagonal D * A + A * diagonal D = diagonal D * A - (diagonal D * A)ᴴ := by
    rw [hc, sub_neg_eq_add]
  rw [selfCommutator_diagonal_add D (fun i => hD i) A hA, norm_neg, norm_sq_two_nsmul,
    mul_self_sub_conjTranspose_mul_self_diagonal_add D (fun i => hD i) A hA, norm_sq_two_nsmul,
    hm, hp, ← frobenius_norm_comp (diagonal D * A + (diagonal D * A)ᴴ),
    ← frobenius_norm_comp (diagonal D * A - (diagonal D * A)ᴴ),
    ← frobenius_norm_comp (diagonal D * A), comp_add_conjTranspose, comp_sub_conjTranspose]
  have par := frobenius_parallelogram (comp ι ι m m ℂ (diagonal D * A))
    (comp ι ι m m ℂ (diagonal D * A))ᴴ
  rw [frobenius_norm_conjTranspose] at par
  linarith

/-- **The two energies, difference.** For Hermitian blocks `D i` and skew-Hermitian `A`,
`‖[H, Hᴴ]‖² / 8 - ‖H * H - Hᴴ * Hᴴ‖² / 8 = 2 re (trace (X * X))`, where
`X = comp (diagonal D * A)` is `D A` as an `(ι × m) × (ι × m)` complex matrix. -/
theorem norm_sq_selfCommutator_sub_norm_sq_mul_self_sub_div_eight (D : ι → Matrix m m ℂ)
    (hD : ∀ i, (D i).IsHermitian) (A : Matrix ι ι (Matrix m m ℂ)) (hA : Aᴴ = -A) :
    ‖(diagonal D + A) * (diagonal D + A)ᴴ - (diagonal D + A)ᴴ * (diagonal D + A)‖ ^ 2 / 8 -
        ‖(diagonal D + A) * (diagonal D + A) - (diagonal D + A)ᴴ * (diagonal D + A)ᴴ‖ ^ 2 / 8 =
      2 * RCLike.re
        (trace (comp ι ι m m ℂ (diagonal D * A) * comp ι ι m m ℂ (diagonal D * A))) := by
  have hstar : star D = D := funext fun i => hD i
  have hc : (diagonal D * A)ᴴ = -(A * diagonal D) := by
    rw [conjTranspose_mul, hA, diagonal_conjTranspose, hstar, Matrix.neg_mul]
  have hm : diagonal D * A - A * diagonal D = diagonal D * A + (diagonal D * A)ᴴ := by
    rw [hc, sub_eq_add_neg]
  have hp : diagonal D * A + A * diagonal D = diagonal D * A - (diagonal D * A)ᴴ := by
    rw [hc, sub_neg_eq_add]
  rw [selfCommutator_diagonal_add D (fun i => hD i) A hA, norm_neg, norm_sq_two_nsmul,
    mul_self_sub_conjTranspose_mul_self_diagonal_add D (fun i => hD i) A hA, norm_sq_two_nsmul,
    hm, hp, ← frobenius_norm_comp (diagonal D * A + (diagonal D * A)ᴴ),
    ← frobenius_norm_comp (diagonal D * A - (diagonal D * A)ᴴ), comp_add_conjTranspose,
    comp_sub_conjTranspose]
  have key := norm_sq_add_conjTranspose_eq (comp ι ι m m ℂ (diagonal D * A))
  linarith

omit [DecidableEq ι] in
/-- **Bipartite swap.** Let every edge of `G` join `S` to its complement. If `D'` agrees with
`D` on `S` and with `-D` off `S`, the connection energy of `D'` is the opposite energy of `D`. -/
theorem connectionEnergy_eq_oppositeEnergy_of_bipartite [DecidableRel G.Adj]
    (A : Matrix ι ι (Matrix m m ℂ)) {S : Set ι} (hS : ∀ i j, G.Adj i j → (i ∈ S ↔ j ∉ S))
    {D D' : ι → Matrix m m ℂ} (h₁ : ∀ i ∈ S, D' i = D i) (h₂ : ∀ i ∉ S, D' i = -D i) :
    connectionEnergy G A D' = oppositeEnergy G A D := by
  rw [connectionEnergy, oppositeEnergy]
  congr 1
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  by_cases hij : G.Adj i j
  · rw [if_pos hij, if_pos hij]
    by_cases hi : i ∈ S
    · rw [h₁ i hi, h₂ j ((hS i j hij).1 hi), Matrix.mul_neg, Matrix.neg_mul, sub_neg_eq_add]
    · have hj : j ∈ S := by
        by_contra hj
        exact hi ((hS i j hij).2 hj)
      rw [h₂ i hi, h₁ j hj, sub_eq_add_neg, ← neg_add, norm_neg]
  · rw [if_neg hij, if_neg hij]

omit [DecidableEq ι] in
/-- **Bipartite swap, the other way.** Under the hypotheses of
`connectionEnergy_eq_oppositeEnergy_of_bipartite`, the opposite energy of `D'` is the connection
energy of `D`. -/
theorem oppositeEnergy_eq_connectionEnergy_of_bipartite [DecidableRel G.Adj]
    (A : Matrix ι ι (Matrix m m ℂ)) {S : Set ι} (hS : ∀ i j, G.Adj i j → (i ∈ S ↔ j ∉ S))
    {D D' : ι → Matrix m m ℂ} (h₁ : ∀ i ∈ S, D' i = D i) (h₂ : ∀ i ∉ S, D' i = -D i) :
    oppositeEnergy G A D' = connectionEnergy G A D :=
  (connectionEnergy_eq_oppositeEnergy_of_bipartite A hS (fun i hi => (h₁ i hi).symm)
    fun i hi => by rw [h₂ i hi, neg_neg]).symm

omit [Fintype ι] [DecidableEq ι] in
/-- An anti-parallel section is transported along a walk `p` by `(-1) ^ p.length` times
conjugation by the holonomy of `p`. -/
theorem IsAntiParallel.eq_conj_holonomy {A : Matrix ι ι (Matrix m m ℂ)} {D : ι → Matrix m m ℂ}
    (hD : IsAntiParallel G A D) {u v : ι} (p : G.Walk u v) :
    D v = (-1 : ℂ) ^ p.length • (holonomy A p * D u * (holonomy A p)ᴴ) := by
  induction p with
  | nil => simp
  | @cons a b c h p ih =>
    rw [ih, hD b a h.symm, holonomy_cons, conjTranspose_mul,
      SimpleGraph.Walk.length_cons, pow_succ]
    simp only [Matrix.mul_neg, Matrix.neg_mul, mul_neg_one, neg_smul, smul_neg, Matrix.mul_assoc]

end NonNormality
