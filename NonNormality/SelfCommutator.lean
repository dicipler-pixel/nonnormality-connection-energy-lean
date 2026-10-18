/-
Copyright (c) 2026 Jeromie Beasley. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeromie Beasley
-/
import Mathlib.Algebra.Star.SelfAdjoint
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.Tactic.NoncommRing
import NonNormality.Frobenius

/-!
# The self-commutator of a block transport operator

Let `G` be a finite simple graph on `ι`. A *block transport operator* is
`H = diagonal D + A : Matrix ι ι (Matrix m m ℂ)` where every diagonal block `D i` is Hermitian and
`A` is skew-Hermitian (`Aᴴ = -A`), supported on the edges of `G`, with unitary edge blocks.
Write `[H, Hᴴ] = H * Hᴴ - Hᴴ * H` for its self-commutator.

## Main results

* `NonNormality.selfCommutator_diagonal_add`: for any star ring, if `star (d i) = d i` and
  `aᴴ = -a` then `[diagonal d + a, (diagonal d + a)ᴴ] = -(2 • (diagonal d * a - a * diagonal d))`.
* `NonNormality.norm_sq_selfCommutator_eq`: `‖[H, Hᴴ]‖² = 4 ∑ i j, ‖D i * A i j - A i j * D j‖²`
  (Frobenius norms; no unitarity needed).
* `NonNormality.norm_sq_selfCommutator_div_eight`: under unitary edge blocks,
  `‖[H, Hᴴ]‖² / 8 = connectionEnergy G A D`, where `connectionEnergy` is the sum over the
  edges `{i, j}` of `‖D i - A i j * D j * (A i j)ᴴ‖²`, written as half the sum over ordered
  adjacent pairs (the convention of `SimpleGraph.lapMatrix_toLinearMap₂'`).
* `NonNormality.norm_sq_selfCommutator_div_eight_eq_sum_edgeFinset`: the same identity with the
  sum taken over `G.edgeFinset`.
* `NonNormality.isStarNormal_iff_isParallel`: `H` is normal iff `D i = A i j * D j * (A i j)ᴴ`
  for every edge.
* `NonNormality.norm_sq_selfCommutator_scalar`: the scalar (`1 × 1` block) case,
  `‖[H, Hᴴ]‖² = 4 ∑ i j, ‖a i j‖² (d i - d j)²`, a weighted Dirichlet form.

## References

* J. Beasley, *Non-normality is connection energy* (2026), identities (1) and (2).
-/

open Matrix
open scoped Matrix.Norms.Frobenius

namespace NonNormality

variable {ι m : Type*} [Fintype ι] [DecidableEq ι] [Fintype m] [DecidableEq m]

section Algebra

variable {R : Type*} [Ring R]

/-- If `d` is entrywise self-adjoint and `a` is skew-Hermitian, the self-commutator of
`diagonal d + a` is `-2` times the commutator `[diagonal d, a]`. -/
theorem selfCommutator_diagonal_add [StarRing R] (d : ι → R) (hd : ∀ i, star (d i) = d i)
    (a : Matrix ι ι R) (ha : aᴴ = -a) :
    (diagonal d + a) * (diagonal d + a)ᴴ - (diagonal d + a)ᴴ * (diagonal d + a) =
      -(2 • (diagonal d * a - a * diagonal d)) := by
  have hstar : star d = d := funext hd
  rw [conjTranspose_add, diagonal_conjTranspose, hstar, ha]
  noncomm_ring

/-- The entries of the commutator `[diagonal d, a]`. -/
theorem diagonal_mul_sub_mul_diagonal_apply (d : ι → R) (a : Matrix ι ι R) (i j : ι) :
    (diagonal d * a - a * diagonal d) i j = d i * a i j - a i j * d j := by
  simp [diagonal_mul, mul_diagonal]

end Algebra

/-- The squared Frobenius norm of `-(2 • X)` is four times that of `X`. -/
private lemma norm_sq_neg_two_nsmul {α : Type*} [NormedAddCommGroup α] [NormedSpace ℝ α]
    (x : α) : ‖-(2 • x)‖ ^ 2 = 4 * ‖x‖ ^ 2 := by
  rw [norm_neg, ← Nat.cast_smul_eq_nsmul ℝ, norm_smul]
  norm_num
  ring

/-- **Frobenius norm of the self-commutator of a block transport operator.** For Hermitian
diagonal blocks `D i` and skew-Hermitian `A`,
`‖[H, Hᴴ]‖² = 4 ∑ i j, ‖D i * A i j - A i j * D j‖²` with `H = diagonal D + A`. -/
theorem norm_sq_selfCommutator_eq (D : ι → Matrix m m ℂ) (hD : ∀ i, (D i).IsHermitian)
    (A : Matrix ι ι (Matrix m m ℂ)) (hA : Aᴴ = -A) :
    ‖(diagonal D + A) * (diagonal D + A)ᴴ - (diagonal D + A)ᴴ * (diagonal D + A)‖ ^ 2 =
      4 * ∑ i, ∑ j, ‖D i * A i j - A i j * D j‖ ^ 2 := by
  rw [selfCommutator_diagonal_add D (fun i => hD i) A hA, frobenius_norm_sq, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Matrix.neg_apply, Matrix.smul_apply, norm_sq_neg_two_nsmul,
    diagonal_mul_sub_mul_diagonal_apply]

variable (G : SimpleGraph ι)

/-- `A` is a unitary connection on `G` with `m × m` blocks: it is skew-Hermitian, vanishes off
the edges of `G` (in particular on the diagonal), and its edge blocks are unitary. Then
`A j i = -(A i j)ᴴ = -(A i j)⁻¹`. -/
structure IsUnitaryConnection (A : Matrix ι ι (Matrix m m ℂ)) : Prop where
  /-- `A` is skew-Hermitian. -/
  conjTranspose_eq_neg : Aᴴ = -A
  /-- `A` is supported on the edges of `G`. -/
  eq_zero_of_not_adj : ∀ i j, ¬ G.Adj i j → A i j = 0
  /-- The edge blocks of `A` are unitary. -/
  mem_unitaryGroup : ∀ i j, G.Adj i j → A i j ∈ unitaryGroup m ℂ

/-- `D` is parallel for the connection induced by `A` on endomorphisms:
`D i = A i j * D j * (A i j)ᴴ` along every edge. -/
def IsParallel (A : Matrix ι ι (Matrix m m ℂ)) (D : ι → Matrix m m ℂ) : Prop :=
  ∀ i j, G.Adj i j → D i = A i j * D j * (A i j)ᴴ

/-- The connection energy of `D`: the sum over the edges `{i, j}` of `G` of
`‖D i - A i j * D j * (A i j)ᴴ‖²` (Frobenius norm), written as half the sum over ordered
adjacent pairs. -/
noncomputable def connectionEnergy [DecidableRel G.Adj] (A : Matrix ι ι (Matrix m m ℂ))
    (D : ι → Matrix m m ℂ) : ℝ :=
  (∑ i, ∑ j, if G.Adj i j then ‖D i - A i j * D j * (A i j)ᴴ‖ ^ 2 else 0) / 2

variable {G}

omit [Fintype ι] [DecidableEq ι] in
/-- The blocks of a unitary connection satisfy `A j i = -(A i j)ᴴ`. -/
theorem IsUnitaryConnection.apply_eq_neg_conjTranspose {A : Matrix ι ι (Matrix m m ℂ)}
    (hA : IsUnitaryConnection G A) (j i : ι) : A j i = -(A i j)ᴴ := by
  have h := congrFun (congrFun hA.conjTranspose_eq_neg j) i
  rw [conjTranspose_apply, Matrix.neg_apply] at h
  rw [← star_eq_conjTranspose, h, neg_neg]

/-- For a unitary edge block, `‖D i * A - A * D j‖ = ‖D i - A * D j * Aᴴ‖`. -/
theorem norm_mul_sub_mul_eq_of_mem_unitaryGroup {U : Matrix m m ℂ} (hU : U ∈ unitaryGroup m ℂ)
    (X Y : Matrix m m ℂ) : ‖X * U - U * Y‖ = ‖X - U * Y * Uᴴ‖ := by
  have h : X * U - U * Y = (X - U * Y * Uᴴ) * U := by
    rw [Matrix.sub_mul, Matrix.mul_assoc (U * Y), ← star_eq_conjTranspose,
      (mem_unitaryGroup_iff').1 hU, Matrix.mul_one]
  rw [h, frobenius_norm_mul_unitary _ hU]

/-- **Identity (1).** For a block transport operator `H = diagonal D + A` with Hermitian
diagonal blocks and a unitary connection `A` on `G`,
`‖[H, Hᴴ]‖² / 8 = connectionEnergy G A D`. -/
theorem norm_sq_selfCommutator_div_eight [DecidableRel G.Adj] {A : Matrix ι ι (Matrix m m ℂ)}
    (hA : IsUnitaryConnection G A) {D : ι → Matrix m m ℂ} (hD : ∀ i, (D i).IsHermitian) :
    ‖(diagonal D + A) * (diagonal D + A)ᴴ - (diagonal D + A)ᴴ * (diagonal D + A)‖ ^ 2 / 8 =
      connectionEnergy G A D := by
  rw [norm_sq_selfCommutator_eq D hD A hA.conjTranspose_eq_neg, connectionEnergy]
  have h : ∀ i j, ‖D i * A i j - A i j * D j‖ ^ 2 =
      if G.Adj i j then ‖D i - A i j * D j * (A i j)ᴴ‖ ^ 2 else 0 := by
    intro i j
    split_ifs with hij
    · rw [norm_mul_sub_mul_eq_of_mem_unitaryGroup (hA.mem_unitaryGroup i j hij)]
    · simp [hA.eq_zero_of_not_adj i j hij]
  simp_rw [h]
  ring

omit [DecidableEq ι] in
/-- The connection energy vanishes exactly on parallel sections:
`connectionEnergy G A D = 0 ↔ IsParallel G A D`. -/
theorem connectionEnergy_eq_zero_iff [DecidableRel G.Adj] (A : Matrix ι ι (Matrix m m ℂ))
    (D : ι → Matrix m m ℂ) :
    connectionEnergy G A D = 0 ↔ IsParallel G A D := by
  have hnn : ∀ i j, 0 ≤ if G.Adj i j then ‖D i - A i j * D j * (A i j)ᴴ‖ ^ 2 else 0 := by
    intro i j; split_ifs <;> positivity
  rw [connectionEnergy, div_eq_zero_iff, or_iff_left two_ne_zero,
    Finset.sum_eq_zero_iff_of_nonneg fun i _ => Finset.sum_nonneg fun j _ => hnn i j]
  simp only [Finset.mem_univ, true_implies]
  refine forall_congr' fun i => ?_
  rw [Finset.sum_eq_zero_iff_of_nonneg fun j _ => hnn i j]
  simp only [Finset.mem_univ, true_implies]
  refine forall_congr' fun j => ?_
  split_ifs with hij
  · simp [hij, sub_eq_zero]
  · simp [hij]

omit [DecidableEq ι] in
/-- `connectionEnergy` is nonnegative. -/
theorem connectionEnergy_nonneg [DecidableRel G.Adj] (A : Matrix ι ι (Matrix m m ℂ))
    (D : ι → Matrix m m ℂ) :
    0 ≤ connectionEnergy G A D := by
  rw [connectionEnergy]
  refine div_nonneg (Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => ?_) zero_le_two
  split_ifs <;> positivity

/-- **Identity (2).** A block transport operator `H = diagonal D + A` with Hermitian diagonal
blocks and a unitary connection `A` on `G` is normal iff `D` is parallel:
`D i = A i j * D j * (A i j)ᴴ` for every edge `{i, j}`. -/
theorem isStarNormal_iff_isParallel {A : Matrix ι ι (Matrix m m ℂ)}
    (hA : IsUnitaryConnection G A) {D : ι → Matrix m m ℂ} (hD : ∀ i, (D i).IsHermitian) :
    IsStarNormal (diagonal D + A) ↔ IsParallel G A D := by
  classical
  rw [← connectionEnergy_eq_zero_iff, ← norm_sq_selfCommutator_div_eight hA hD,
    isStarNormal_iff, Commute, SemiconjBy, star_eq_conjTranspose]
  constructor
  · intro h; rw [h, sub_self, norm_zero]; norm_num
  · intro h
    have h0 : ‖(diagonal D + A) * (diagonal D + A)ᴴ - (diagonal D + A)ᴴ * (diagonal D + A)‖ =
        0 := by
      have : ‖(diagonal D + A) * (diagonal D + A)ᴴ -
          (diagonal D + A)ᴴ * (diagonal D + A)‖ ^ 2 = 0 := by linarith
      exact pow_eq_zero_iff two_ne_zero |>.1 this
    exact (sub_eq_zero.1 (norm_eq_zero.1 h0)).symm

omit [Fintype ι] [DecidableEq ι] in
/-- The summand `‖D i * A i j - A i j * D j‖` is symmetric in `i` and `j`. -/
theorem IsUnitaryConnection.norm_mul_sub_mul_comm {A : Matrix ι ι (Matrix m m ℂ)}
    (hA : IsUnitaryConnection G A) {D : ι → Matrix m m ℂ} (hD : ∀ i, (D i).IsHermitian)
    (i j : ι) : ‖D j * A j i - A j i * D i‖ = ‖D i * A i j - A i j * D j‖ := by
  rw [hA.apply_eq_neg_conjTranspose j i]
  generalize A i j = U
  rw [← frobenius_norm_conjTranspose (D i * U - U * D j), conjTranspose_sub, conjTranspose_mul,
    conjTranspose_mul, (hD i).eq, (hD j).eq]
  congr 1
  noncomm_ring

omit [Fintype ι] [DecidableEq ι] in
/-- On an edge, the summand of `connectionEnergy` does not depend on the orientation. -/
theorem IsUnitaryConnection.norm_sub_conj_comm {A : Matrix ι ι (Matrix m m ℂ)}
    (hA : IsUnitaryConnection G A) {D : ι → Matrix m m ℂ} (hD : ∀ i, (D i).IsHermitian)
    {i j : ι} (hij : G.Adj i j) :
    ‖D j - A j i * D i * (A j i)ᴴ‖ = ‖D i - A i j * D j * (A i j)ᴴ‖ := by
  rw [← norm_mul_sub_mul_eq_of_mem_unitaryGroup (hA.mem_unitaryGroup j i hij.symm),
    ← norm_mul_sub_mul_eq_of_mem_unitaryGroup (hA.mem_unitaryGroup i j hij),
    hA.norm_mul_sub_mul_comm hD]

omit [DecidableEq ι] in
/-- Summing a symmetric function over ordered adjacent pairs counts every edge twice. -/
theorem sum_sum_ite_adj_eq_two_mul_sum_edgeFinset [DecidableRel G.Adj] {M : Type*}
    [AddCommMonoid M]
    (f : ι → ι → M) (hf : ∀ i j, f i j = f j i) :
    (∑ i, ∑ j, if G.Adj i j then f i j else 0) =
      2 • ∑ e ∈ G.edgeFinset, Sym2.lift ⟨f, hf⟩ e := by
  classical
  rw [← Finset.sum_product' (f := fun i j => if G.Adj i j then f i j else 0),
    ← Finset.sum_filter, Finset.smul_sum]
  have hmaps : ∀ p ∈ {p ∈ (Finset.univ : Finset ι) ×ˢ (Finset.univ : Finset ι) | G.Adj p.1 p.2},
      s(p.1, p.2) ∈ G.edgeFinset := by
    intro p hp
    simpa using (Finset.mem_filter.1 hp).2
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  refine Finset.sum_congr rfl fun e he => ?_
  induction e using Sym2.ind with
  | _ a b =>
  have hab : G.Adj a b := by simpa using he
  have hfib : {p ∈ {p ∈ (Finset.univ : Finset ι) ×ˢ (Finset.univ : Finset ι) | G.Adj p.1 p.2} |
      s(p.1, p.2) = s(a, b)} = {(a, b), (b, a)} := by
    ext ⟨x, y⟩
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_univ, true_and,
      Finset.mem_insert, Finset.mem_singleton, Sym2.eq_iff, Prod.mk.injEq]
    constructor
    · rintro ⟨-, h⟩; exact h
    · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
      · exact ⟨hab, Or.inl ⟨rfl, rfl⟩⟩
      · exact ⟨hab.symm, Or.inr ⟨rfl, rfl⟩⟩
  have hne : (a, b) ≠ (b, a) := fun h => hab.ne (Prod.mk.inj h).1
  rw [hfib, Finset.sum_pair hne, Sym2.lift_mk, hf b a, two_nsmul]

/-- **Identity (1), edge form.** `‖[H, Hᴴ]‖² / 8` is the sum over the edges `{i, j}` of `G` of
`‖D i - A i j * D j * (A i j)ᴴ‖²`; the summand is independent of the orientation of the edge
(`norm_sub_conj_comm`). The summand is written symmetrically as `‖D i * A i j - A i j * D j‖²`,
which equals `‖D i - A i j * D j * (A i j)ᴴ‖²` on edges
(`norm_mul_sub_mul_eq_of_mem_unitaryGroup`). -/
theorem norm_sq_selfCommutator_div_eight_eq_sum_edgeFinset [DecidableRel G.Adj]
    {A : Matrix ι ι (Matrix m m ℂ)}
    (hA : IsUnitaryConnection G A) {D : ι → Matrix m m ℂ} (hD : ∀ i, (D i).IsHermitian) :
    ‖(diagonal D + A) * (diagonal D + A)ᴴ - (diagonal D + A)ᴴ * (diagonal D + A)‖ ^ 2 / 8 =
      ∑ e ∈ G.edgeFinset, Sym2.lift ⟨fun i j => ‖D i * A i j - A i j * D j‖ ^ 2,
        fun i j => by simp only [hA.norm_mul_sub_mul_comm hD]⟩ e := by
  rw [norm_sq_selfCommutator_eq D hD A hA.conjTranspose_eq_neg]
  have h : ∀ i j, ‖D i * A i j - A i j * D j‖ ^ 2 =
      if G.Adj i j then ‖D i * A i j - A i j * D j‖ ^ 2 else 0 := by
    intro i j
    split_ifs with hij
    · rfl
    · rw [hA.eq_zero_of_not_adj i j hij, Matrix.mul_zero, Matrix.zero_mul, sub_zero, norm_zero,
        sq, mul_zero]
  rw [Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => h i j,
    sum_sum_ite_adj_eq_two_mul_sum_edgeFinset _ fun i j => by
      simp only [hA.norm_mul_sub_mul_comm hD], nsmul_eq_mul]
  ring

/-- **Scalar specialization.** For real potentials `d` and a skew-Hermitian `a : Matrix ι ι ℂ`,
`‖[H, Hᴴ]‖² = 4 ∑ i j, ‖a i j‖² (d i - d j)²` with `H = diagonal d + a`: the self-commutator
energy is a weighted Dirichlet form with weights `‖a i j‖²`. -/
theorem norm_sq_selfCommutator_scalar (d : ι → ℝ) (a : Matrix ι ι ℂ) (ha : aᴴ = -a) :
    ‖(diagonal (fun i => (d i : ℂ)) + a) * (diagonal (fun i => (d i : ℂ)) + a)ᴴ -
        (diagonal (fun i => (d i : ℂ)) + a)ᴴ * (diagonal (fun i => (d i : ℂ)) + a)‖ ^ 2 =
      4 * ∑ i, ∑ j, ‖a i j‖ ^ 2 * (d i - d j) ^ 2 := by
  rw [selfCommutator_diagonal_add _ (fun i => Complex.conj_ofReal (d i)) a ha, frobenius_norm_sq,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Matrix.neg_apply, Matrix.smul_apply, norm_sq_neg_two_nsmul,
    diagonal_mul_sub_mul_diagonal_apply,
    mul_comm (a i j), ← sub_mul, norm_mul, ← Complex.ofReal_sub, Complex.norm_real,
    Real.norm_eq_abs, mul_pow, sq_abs]
  ring

end NonNormality
