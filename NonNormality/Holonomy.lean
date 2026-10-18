/-
Copyright (c) 2026 Jeromie Beasley. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeromie Beasley
-/
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.LinearAlgebra.Basis.VectorSpace
import NonNormality.SelfCommutator

/-!
# Parallel sections and holonomy

Let `A` be a unitary connection on a graph `G` (`NonNormality.IsUnitaryConnection`). Transport of
an endomorphism `X` of the fibre at `j` to the fibre at `i` along an edge is
`X ↦ A i j * X * (A i j)ᴴ`. Along a walk `p` from `u` to `v` the transport is conjugation by
`NonNormality.holonomy A p`, the product of the edge blocks along `p`.

## Main results

* `NonNormality.IsParallel.eq_conj_holonomy`: a parallel section satisfies
  `D v = holonomy A p * D u * (holonomy A p)ᴴ` for every walk `p` from `u` to `v`.
* `NonNormality.holonomy_reverse`: `holonomy A p.reverse = (-1) ^ p.length • (holonomy A p)ᴴ`;
  reversing a walk inverts its holonomy up to the central sign coming from `A j i = -(A i j)ᴴ`.
* `NonNormality.parallelSectionsEquivHolonomyFixed`: **identity (3).** If `G` is connected,
  evaluation at a base vertex `i₀` is an `ℝ`-linear equivalence from Hermitian parallel sections
  (the zero set of `NonNormality.connectionEnergy`, equivalently the `D` with `diagonal D + A`
  normal) onto the Hermitian matrices fixed by conjugation by the holonomy of every loop at `i₀`.
* `NonNormality.mem_holonomyFixed_iff_commute`: such matrices are exactly the Hermitian matrices
  commuting with every loop holonomy.

## References

* J. Beasley, *Non-normality is connection energy* (2026), identity (3).
-/

open Matrix SimpleGraph

namespace NonNormality

variable {ι m : Type*} [Fintype m] [DecidableEq m] {G : SimpleGraph ι}

/-- The holonomy of a walk: the product of the edge blocks of `A` along the walk, the first edge
acting first. For `p : G.Walk u v` it maps the fibre at `u` to the fibre at `v`. -/
def holonomy (A : Matrix ι ι (Matrix m m ℂ)) : {u v : ι} → G.Walk u v → Matrix m m ℂ
  | _, _, Walk.nil => 1
  | u, _, Walk.cons (v := w) _ p => holonomy A p * A w u

variable (A : Matrix ι ι (Matrix m m ℂ))

@[simp]
theorem holonomy_nil (u : ι) : holonomy A (Walk.nil : G.Walk u u) = 1 := rfl

@[simp]
theorem holonomy_cons {u v w : ι} (h : G.Adj u v) (p : G.Walk v w) :
    holonomy A (Walk.cons h p) = holonomy A p * A v u := rfl

theorem holonomy_append {u v w : ι} (p : G.Walk u v) (q : G.Walk v w) :
    holonomy A (p.append q) = holonomy A q * holonomy A p := by
  induction p with
  | nil => simp
  | cons h p ih => rw [Walk.cons_append, holonomy_cons, holonomy_cons, ih, Matrix.mul_assoc]

theorem holonomy_concat {u v w : ι} (p : G.Walk u v) (h : G.Adj v w) :
    holonomy A (p.concat h) = A w v * holonomy A p := by
  rw [Walk.concat_eq_append, holonomy_append, holonomy_cons, holonomy_nil, Matrix.one_mul]

variable {A}

/-- The holonomy of a walk along a unitary connection is unitary. -/
theorem IsUnitaryConnection.holonomy_mem_unitaryGroup
    (hA : IsUnitaryConnection G A) {u v : ι} (p : G.Walk u v) :
    holonomy A p ∈ unitaryGroup m ℂ := by
  induction p with
  | nil => exact one_mem _
  | cons h p ih => exact mul_mem ih (hA.mem_unitaryGroup _ _ h.symm)

/-- Reversing a walk inverts its holonomy, up to the central sign `(-1) ^ p.length`. -/
theorem IsUnitaryConnection.holonomy_reverse
    (hA : IsUnitaryConnection G A) {u v : ι} (p : G.Walk u v) :
    holonomy A p.reverse = (-1 : ℂ) ^ p.length • (holonomy A p)ᴴ := by
  induction p with
  | nil => simp
  | @cons a b c h p ih =>
    rw [Walk.reverse_cons, holonomy_append, holonomy_cons, holonomy_nil, Matrix.one_mul, ih,
      hA.apply_eq_neg_conjTranspose a b, holonomy_cons, conjTranspose_mul, Walk.length_cons,
      pow_succ, mul_comm, mul_smul, Matrix.mul_smul, neg_one_smul, Matrix.neg_mul, smul_neg]

omit [DecidableEq m] in
/-- Conjugation by `c • U` with `c = ± 1` is conjugation by `U`. -/
private lemma conj_neg_one_pow_smul (n : ℕ) (U X : Matrix m m ℂ) :
    ((-1 : ℂ) ^ n • U) * X * ((-1 : ℂ) ^ n • U)ᴴ = U * X * Uᴴ := by
  rw [conjTranspose_smul, star_pow, star_neg, star_one, Matrix.smul_mul, Matrix.smul_mul,
    Matrix.mul_smul, smul_smul, ← mul_pow, neg_one_mul, neg_neg, one_pow, one_smul]

/-- For a unitary `U`, `U * X * Uᴴ = X` iff `U` commutes with `X`. -/
theorem conj_eq_self_iff_commute {U : Matrix m m ℂ} (hU : U ∈ unitaryGroup m ℂ)
    (X : Matrix m m ℂ) : U * X * Uᴴ = X ↔ Commute U X := by
  have h₁ : Uᴴ * U = 1 := (mem_unitaryGroup_iff').1 hU
  constructor
  · intro h
    change U * X = X * U
    calc U * X = U * X * Uᴴ * U := by rw [Matrix.mul_assoc _ Uᴴ, h₁, Matrix.mul_one]
      _ = X * U := by rw [h]
  · intro h
    rw [h.eq, Matrix.mul_assoc, ← star_eq_conjTranspose, (mem_unitaryGroup_iff).1 hU,
      Matrix.mul_one]

/-- A parallel section is transported by the holonomy along every walk. -/
theorem IsParallel.eq_conj_holonomy {D : ι → Matrix m m ℂ}
    (hD : IsParallel G A D) {u v : ι} (p : G.Walk u v) :
    D v = holonomy A p * D u * (holonomy A p)ᴴ := by
  induction p with
  | nil => simp
  | @cons a b c h p ih =>
    rw [ih, hD b a h.symm, holonomy_cons, conjTranspose_mul]
    simp only [Matrix.mul_assoc]

variable (G A) in
/-- The Hermitian matrices fixed by conjugation by the holonomy of every loop at `i₀`. -/
def holonomyFixed (i₀ : ι) : Submodule ℝ (Matrix m m ℂ) where
  carrier := {X | X.IsHermitian ∧ ∀ p : G.Walk i₀ i₀, holonomy A p * X * (holonomy A p)ᴴ = X}
  add_mem' {X Y} hX hY :=
    ⟨hX.1.add hY.1, fun p => by rw [Matrix.mul_add, Matrix.add_mul, hX.2 p, hY.2 p]⟩
  zero_mem' := ⟨isHermitian_zero, fun p => by rw [Matrix.mul_zero, Matrix.zero_mul]⟩
  smul_mem' c X hX :=
    ⟨hX.1.smul (IsSelfAdjoint.all c), fun p => by
      rw [Matrix.mul_smul, Matrix.smul_mul, hX.2 p]⟩

variable (G A) in
/-- Hermitian sections `D` that are parallel for the connection induced by `A`. By
`connectionEnergy_eq_zero_iff` these form the zero set of `connectionEnergy G A`, and by
`isStarNormal_iff_isParallel` they are the `D` for which `diagonal D + A` is normal. -/
def parallelSections : Submodule ℝ (ι → Matrix m m ℂ) where
  carrier := {D | (∀ i, (D i).IsHermitian) ∧ IsParallel G A D}
  add_mem' {D E} hD hE :=
    ⟨fun i => (hD.1 i).add (hE.1 i), fun i j h => by
      rw [Pi.add_apply, Pi.add_apply, hD.2 i j h, hE.2 i j h, Matrix.mul_add, Matrix.add_mul]⟩
  zero_mem' := ⟨fun _ => isHermitian_zero, fun i j _ => by simp⟩
  smul_mem' c D hD :=
    ⟨fun i => (hD.1 i).smul (IsSelfAdjoint.all c), fun i j h => by
      rw [Pi.smul_apply, Pi.smul_apply, hD.2 i j h, Matrix.mul_smul, Matrix.smul_mul]⟩

theorem mem_parallelSections_iff {D : ι → Matrix m m ℂ} :
    D ∈ parallelSections G A ↔ (∀ i, (D i).IsHermitian) ∧ IsParallel G A D := Iff.rfl

/-- For Hermitian `D`, membership in `parallelSections` is the vanishing of the connection
energy, i.e. the normality of `diagonal D + A` (`isStarNormal_iff_isParallel`). -/
theorem mem_parallelSections_iff_connectionEnergy_eq_zero [Fintype ι] [DecidableRel G.Adj]
    {D : ι → Matrix m m ℂ}
    (hD : ∀ i, (D i).IsHermitian) :
    D ∈ parallelSections G A ↔ connectionEnergy G A D = 0 := by
  rw [mem_parallelSections_iff, connectionEnergy_eq_zero_iff]
  exact and_iff_right hD

theorem mem_holonomyFixed_iff {i₀ : ι} {X : Matrix m m ℂ} :
    X ∈ holonomyFixed G A i₀ ↔
      X.IsHermitian ∧ ∀ p : G.Walk i₀ i₀, holonomy A p * X * (holonomy A p)ᴴ = X := Iff.rfl

/-- The holonomy-fixed Hermitian matrices are the Hermitian matrices commuting with the holonomy
of every loop at `i₀`. -/
theorem IsUnitaryConnection.mem_holonomyFixed_iff_commute (hA : IsUnitaryConnection G A)
    {i₀ : ι} {X : Matrix m m ℂ} :
    X ∈ holonomyFixed G A i₀ ↔
      X.IsHermitian ∧ ∀ p : G.Walk i₀ i₀, Commute X (holonomy A p) := by
  rw [mem_holonomyFixed_iff]
  refine and_congr_right fun _ => forall_congr' fun p => ?_
  rw [conj_eq_self_iff_commute (hA.holonomy_mem_unitaryGroup p), Commute.symm_iff]

/-- Any two walks from `i₀` to `v` transport a holonomy-fixed matrix to the same matrix. -/
theorem IsUnitaryConnection.conj_holonomy_eq (hA : IsUnitaryConnection G A) {i₀ v : ι}
    {X : Matrix m m ℂ} (hX : X ∈ holonomyFixed G A i₀) (p q : G.Walk i₀ v) :
    holonomy A p * X * (holonomy A p)ᴴ = holonomy A q * X * (holonomy A q)ᴴ := by
  have hloop := hX.2 (p.append q.reverse)
  rw [holonomy_append, hA.holonomy_reverse, Matrix.smul_mul, conj_neg_one_pow_smul] at hloop
  have hq₁ : holonomy A q * (holonomy A q)ᴴ = 1 :=
    (mem_unitaryGroup_iff).1 (hA.holonomy_mem_unitaryGroup q)
  calc holonomy A p * X * (holonomy A p)ᴴ
      = holonomy A q * (holonomy A q)ᴴ * (holonomy A p * X * (holonomy A p)ᴴ) *
          (holonomy A q * (holonomy A q)ᴴ) := by rw [hq₁, Matrix.one_mul, Matrix.mul_one]
    _ = holonomy A q * ((holonomy A q)ᴴ * holonomy A p * X * ((holonomy A q)ᴴ * holonomy A p)ᴴ) *
          (holonomy A q)ᴴ := by
        rw [conjTranspose_mul, conjTranspose_conjTranspose]; simp only [Matrix.mul_assoc]
    _ = holonomy A q * X * (holonomy A q)ᴴ := by rw [hloop]

variable (G A) in
/-- Evaluation of a parallel section at the base vertex `i₀`, as a linear map to the
holonomy-fixed Hermitian matrices. -/
def evalParallel (i₀ : ι) : parallelSections G A →ₗ[ℝ] holonomyFixed G A i₀ where
  toFun D := ⟨D.1 i₀, D.2.1 i₀, fun p => (D.2.2.eq_conj_holonomy p).symm⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp]
theorem evalParallel_apply_coe (i₀ : ι) (D : parallelSections G A) :
    (evalParallel G A i₀ D : Matrix m m ℂ) = (D : ι → Matrix m m ℂ) i₀ := rfl

/-- On a connected graph a parallel section is determined by its value at one vertex. -/
theorem evalParallel_injective (hG : G.Connected) (i₀ : ι) :
    Function.Injective (evalParallel G A i₀) := by
  intro D E h
  have h₀ : (D : ι → Matrix m m ℂ) i₀ = (E : ι → Matrix m m ℂ) i₀ := congrArg Subtype.val h
  ext1
  funext v
  obtain ⟨p⟩ := hG.preconnected i₀ v
  rw [D.2.2.eq_conj_holonomy p, E.2.2.eq_conj_holonomy p, h₀]

/-- On a connected graph every holonomy-fixed Hermitian matrix at `i₀` extends to a parallel
section, by transporting it along any walk from `i₀`. -/
theorem IsUnitaryConnection.evalParallel_surjective (hA : IsUnitaryConnection G A)
    (hG : G.Connected) (i₀ : ι) : Function.Surjective (evalParallel G A i₀) := by
  rintro ⟨X, hX⟩
  let w : ∀ v, G.Walk i₀ v := fun v => (hG.preconnected i₀ v).some
  let D : ι → Matrix m m ℂ := fun v => holonomy A (w v) * X * (holonomy A (w v))ᴴ
  have hherm : ∀ v, (D v).IsHermitian := fun v => by
    change (holonomy A (w v) * X * (holonomy A (w v))ᴴ)ᴴ = _
    rw [conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose, hX.1.eq,
      ← Matrix.mul_assoc]
  have hpar : IsParallel G A D := by
    intro i j h
    change holonomy A (w i) * X * (holonomy A (w i))ᴴ = A i j * D j * (A i j)ᴴ
    rw [hA.conj_holonomy_eq hX (w i) ((w j).concat h.symm), holonomy_concat]
    change _ = A i j * (holonomy A (w j) * X * (holonomy A (w j))ᴴ) * (A i j)ᴴ
    rw [conjTranspose_mul]
    simp only [Matrix.mul_assoc]
  refine ⟨⟨D, hherm, hpar⟩, Subtype.ext ?_⟩
  change holonomy A (w i₀) * X * (holonomy A (w i₀))ᴴ = X
  rw [hA.conj_holonomy_eq hX (w i₀) Walk.nil, holonomy_nil, Matrix.one_mul,
    conjTranspose_one, Matrix.mul_one]

/-- **Identity (3).** On a connected graph, evaluation at a base vertex `i₀` is an `ℝ`-linear
equivalence between the Hermitian parallel sections of the connection induced by a unitary
connection `A` (the zero set of the self-commutator energy of `diagonal D + A`) and the
Hermitian matrices fixed by the holonomy of every loop at `i₀`. -/
noncomputable def parallelSectionsEquivHolonomyFixed (hA : IsUnitaryConnection G A)
    (hG : G.Connected) (i₀ : ι) : parallelSections G A ≃ₗ[ℝ] holonomyFixed G A i₀ :=
  LinearEquiv.ofBijective (evalParallel G A i₀)
    ⟨evalParallel_injective hG i₀, hA.evalParallel_surjective hG i₀⟩

@[simp]
theorem parallelSectionsEquivHolonomyFixed_apply_coe (hA : IsUnitaryConnection G A)
    (hG : G.Connected) (i₀ : ι) (D : parallelSections G A) :
    (parallelSectionsEquivHolonomyFixed hA hG i₀ D : Matrix m m ℂ) =
      (D : ι → Matrix m m ℂ) i₀ := rfl

end NonNormality
