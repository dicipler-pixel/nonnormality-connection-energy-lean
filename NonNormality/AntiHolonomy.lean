/-
Copyright (c) 2026 Jeromie Beasley. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeromie Beasley
-/
import NonNormality.Opposite

/-!
# Anti-parallel sections and the parity-twisted holonomy

The mirror of `NonNormality.Holonomy` for the opposite energy. An anti-parallel section
(`NonNormality.IsAntiParallel`: `D i = -(A i j * D j * (A i j)ᴴ)` on every edge) is transported
along a walk `p` by `(-1) ^ p.length` times conjugation by the holonomy
(`IsAntiParallel.eq_conj_holonomy`). The parity-twisted holonomy action at a base vertex `i₀`
fixes a Hermitian matrix `X` when `(-1) ^ p.length • (holonomy A p * X * (holonomy A p)ᴴ) = X` for
every closed walk `p` at `i₀`.

## Main results

* `NonNormality.antiParallelSectionsEquivTwistedHolonomyFixed`: **the twisted kernel.** On a
  connected graph, evaluation at `i₀` is an `ℝ`-linear equivalence from the Hermitian
  anti-parallel sections (the zero set of `NonNormality.oppositeEnergy`) onto the Hermitian
  matrices fixed by the parity-twisted holonomy of every closed walk at `i₀`.
* `NonNormality.IsUnitaryConnection.eq_zero_of_mem_twistedHolonomyFixed_of_odd`,
  `NonNormality.IsAntiParallel.eq_zero_of_odd_loop`: an odd closed walk whose holonomy commutes
  with the field kills it; on a connected graph every anti-parallel section then vanishes
  (`IsAntiParallel.eq_zero_of_odd_loop_of_connected`).
* `NonNormality.isParallel_iff_isAntiParallel_of_bipartite`,
  `NonNormality.antiParallelSectionsEquivParallelSections`: on a bipartite graph the sign flip on
  one side exchanges parallel and anti-parallel sections.

## References

* J. Beasley, *Non-normality is connection energy* (2026), v11: the two books.
-/

open Matrix SimpleGraph

namespace NonNormality

variable {ι m : Type*} {G : SimpleGraph ι} {A : Matrix ι ι (Matrix m m ℂ)}

section Sections

variable (G A) in
/-- Hermitian sections `D` that are anti-parallel for the connection induced by `A`. By
`oppositeEnergy_eq_zero_iff` these form the zero set of `oppositeEnergy G A`. -/
def antiParallelSections [Fintype m] : Submodule ℝ (ι → Matrix m m ℂ) where
  carrier := {D | (∀ i, (D i).IsHermitian) ∧ IsAntiParallel G A D}
  add_mem' {D E} hD hE :=
    ⟨fun i => (hD.1 i).add (hE.1 i), fun i j h => by
      rw [Pi.add_apply, Pi.add_apply, hD.2 i j h, hE.2 i j h, Matrix.mul_add, Matrix.add_mul,
        neg_add]⟩
  zero_mem' := ⟨fun _ => isHermitian_zero, fun i j _ => by simp⟩
  smul_mem' c D hD :=
    ⟨fun i => (hD.1 i).smul (IsSelfAdjoint.all c), fun i j h => by
      rw [Pi.smul_apply, Pi.smul_apply, hD.2 i j h, Matrix.mul_smul, Matrix.smul_mul, smul_neg]⟩

theorem mem_antiParallelSections_iff [Fintype m] {D : ι → Matrix m m ℂ} :
    D ∈ antiParallelSections G A ↔ (∀ i, (D i).IsHermitian) ∧ IsAntiParallel G A D := Iff.rfl

/-- For Hermitian `D`, membership in `antiParallelSections` is the vanishing of the opposite
energy, i.e. `H * H = Hᴴ * Hᴴ` (`mul_self_eq_conjTranspose_mul_self_iff_isAntiParallel`). -/
theorem mem_antiParallelSections_iff_oppositeEnergy_eq_zero [Fintype ι] [DecidableRel G.Adj]
    [Fintype m] [DecidableEq m] {D : ι → Matrix m m ℂ} (hD : ∀ i, (D i).IsHermitian) :
    D ∈ antiParallelSections G A ↔ oppositeEnergy G A D = 0 := by
  rw [mem_antiParallelSections_iff, oppositeEnergy_eq_zero_iff]
  exact and_iff_right hD

end Sections

section Twisted

/-- `(-1) ^ n • M` is Hermitian when `M` is. -/
private lemma isHermitian_neg_one_pow_smul {n : ℕ} {M : Matrix m m ℂ} (hM : M.IsHermitian) :
    ((-1 : ℂ) ^ n • M).IsHermitian :=
  hM.smul ((IsSelfAdjoint.one.neg).pow n)

/-- Conjugation by `c • U` with `c = ± 1` is conjugation by `U`. -/
private lemma conj_neg_one_pow_smul [Fintype m] (n : ℕ) (U X : Matrix m m ℂ) :
    ((-1 : ℂ) ^ n • U) * X * ((-1 : ℂ) ^ n • U)ᴴ = U * X * Uᴴ := by
  rw [conjTranspose_smul, star_pow, star_neg, star_one, Matrix.smul_mul, Matrix.smul_mul,
    Matrix.mul_smul, smul_smul, ← mul_pow, neg_one_mul, neg_neg, one_pow, one_smul]

variable (G A) in
/-- The Hermitian matrices fixed by the parity-twisted holonomy of every closed walk at `i₀`:
`(-1) ^ p.length • (holonomy A p * X * (holonomy A p)ᴴ) = X`. -/
def twistedHolonomyFixed [Fintype m] [DecidableEq m] (i₀ : ι) : Submodule ℝ (Matrix m m ℂ) where
  carrier := {X | X.IsHermitian ∧
    ∀ p : G.Walk i₀ i₀, (-1 : ℂ) ^ p.length • (holonomy A p * X * (holonomy A p)ᴴ) = X}
  add_mem' {X Y} hX hY :=
    ⟨hX.1.add hY.1, fun p => by
      rw [Matrix.mul_add, Matrix.add_mul, smul_add, hX.2 p, hY.2 p]⟩
  zero_mem' := ⟨isHermitian_zero, fun p => by rw [Matrix.mul_zero, Matrix.zero_mul, smul_zero]⟩
  smul_mem' c X hX :=
    ⟨hX.1.smul (IsSelfAdjoint.all c), fun p => by
      rw [Matrix.mul_smul, Matrix.smul_mul, smul_comm, hX.2 p]⟩

theorem mem_twistedHolonomyFixed_iff [Fintype m] [DecidableEq m] {i₀ : ι} {X : Matrix m m ℂ} :
    X ∈ twistedHolonomyFixed G A i₀ ↔ X.IsHermitian ∧
      ∀ p : G.Walk i₀ i₀, (-1 : ℂ) ^ p.length • (holonomy A p * X * (holonomy A p)ᴴ) = X :=
  Iff.rfl

/-- **Odd loops kill the twisted fixed set.** If some closed walk at `i₀` has odd length and its
holonomy commutes with `X`, then a twisted-fixed `X` is zero. -/
theorem IsUnitaryConnection.eq_zero_of_mem_twistedHolonomyFixed_of_odd [Fintype m] [DecidableEq m]
    (hA : IsUnitaryConnection G A) {i₀ : ι} {X : Matrix m m ℂ}
    (hX : X ∈ twistedHolonomyFixed G A i₀) (p : G.Walk i₀ i₀) (hp : Odd p.length)
    (hc : Commute (holonomy A p) X) : X = 0 := by
  have h := hX.2 p
  rw [(conj_eq_self_iff_commute (hA.holonomy_mem_unitaryGroup p) X).2 hc, hp.neg_one_pow,
    neg_one_smul] at h
  exact eq_zero_of_eq_of_eq_neg rfl h.symm

/-- **Odd loops kill anti-parallel sections at the base vertex.** -/
theorem IsAntiParallel.eq_zero_of_odd_loop [Fintype m] [DecidableEq m] {D : ι → Matrix m m ℂ}
    (hD : IsAntiParallel G A D) (hA : IsUnitaryConnection G A) {i₀ : ι} (p : G.Walk i₀ i₀)
    (hp : Odd p.length) (hc : Commute (holonomy A p) (D i₀)) : D i₀ = 0 := by
  have h := hD.eq_conj_holonomy p
  rw [(conj_eq_self_iff_commute (hA.holonomy_mem_unitaryGroup p) (D i₀)).2 hc, hp.neg_one_pow,
    neg_one_smul] at h
  exact eq_zero_of_eq_of_eq_neg rfl h

/-- **Odd loops kill anti-parallel sections everywhere** on a connected graph. -/
theorem IsAntiParallel.eq_zero_of_odd_loop_of_connected [Fintype m] [DecidableEq m]
    {D : ι → Matrix m m ℂ} (hD : IsAntiParallel G A D) (hA : IsUnitaryConnection G A)
    (hG : G.Connected) {i₀ : ι} (p : G.Walk i₀ i₀) (hp : Odd p.length)
    (hc : Commute (holonomy A p) (D i₀)) (v : ι) : D v = 0 := by
  obtain ⟨q⟩ := hG.preconnected i₀ v
  rw [hD.eq_conj_holonomy q, hD.eq_zero_of_odd_loop hA p hp hc, Matrix.mul_zero,
    Matrix.zero_mul, smul_zero]

/-- Any two walks from `i₀` to `v` transport a twisted-fixed matrix to the same matrix. -/
theorem IsUnitaryConnection.twisted_conj_holonomy_eq [Fintype m] [DecidableEq m]
    (hA : IsUnitaryConnection G A) {i₀ v : ι} {X : Matrix m m ℂ}
    (hX : X ∈ twistedHolonomyFixed G A i₀) (p q : G.Walk i₀ v) :
    (-1 : ℂ) ^ p.length • (holonomy A p * X * (holonomy A p)ᴴ) =
      (-1 : ℂ) ^ q.length • (holonomy A q * X * (holonomy A q)ᴴ) := by
  have hloop := hX.2 (p.append q.reverse)
  rw [holonomy_append, hA.holonomy_reverse, Matrix.smul_mul, conj_neg_one_pow_smul,
    Walk.length_append, Walk.length_reverse] at hloop
  have hq₁ : holonomy A q * (holonomy A q)ᴴ = 1 :=
    (mem_unitaryGroup_iff).1 (hA.holonomy_mem_unitaryGroup q)
  have h1 : (-1 : ℂ) ^ (p.length + q.length) • (holonomy A p * X * (holonomy A p)ᴴ) =
      holonomy A q * X * (holonomy A q)ᴴ := by
    have h : holonomy A q * ((-1 : ℂ) ^ (p.length + q.length) •
        ((holonomy A q)ᴴ * holonomy A p * X * ((holonomy A q)ᴴ * holonomy A p)ᴴ)) *
          (holonomy A q)ᴴ = holonomy A q * X * (holonomy A q)ᴴ := by
      rw [hloop]
    rw [← h, Matrix.mul_smul, Matrix.smul_mul, conjTranspose_mul, conjTranspose_conjTranspose]
    congr 1
    calc holonomy A p * X * (holonomy A p)ᴴ
        = (holonomy A q * (holonomy A q)ᴴ) * (holonomy A p * X * (holonomy A p)ᴴ) *
            (holonomy A q * (holonomy A q)ᴴ) := by rw [hq₁, Matrix.one_mul, Matrix.mul_one]
      _ = holonomy A q * ((holonomy A q)ᴴ * holonomy A p * X * ((holonomy A p)ᴴ * holonomy A q)) *
            (holonomy A q)ᴴ := by simp only [Matrix.mul_assoc]
  have hs : (-1 : ℂ) ^ q.length * (-1 : ℂ) ^ (p.length + q.length) = (-1 : ℂ) ^ p.length := by
    rw [pow_add, mul_comm, mul_assoc, ← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow, mul_one]
  rw [← h1, smul_smul, hs]

variable (G A) in
/-- Evaluation of an anti-parallel section at the base vertex `i₀`, as a linear map to the
twisted-holonomy-fixed Hermitian matrices. -/
def evalAntiParallel [Fintype m] [DecidableEq m] (i₀ : ι) :
    antiParallelSections G A →ₗ[ℝ] twistedHolonomyFixed G A i₀ where
  toFun D := ⟨D.1 i₀, D.2.1 i₀, fun p => (D.2.2.eq_conj_holonomy p).symm⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp]
theorem evalAntiParallel_apply_coe [Fintype m] [DecidableEq m] (i₀ : ι)
    (D : antiParallelSections G A) :
    (evalAntiParallel G A i₀ D : Matrix m m ℂ) = (D : ι → Matrix m m ℂ) i₀ := rfl

/-- On a connected graph an anti-parallel section is determined by its value at one vertex. -/
theorem evalAntiParallel_injective [Fintype m] [DecidableEq m] (hG : G.Connected) (i₀ : ι) :
    Function.Injective (evalAntiParallel G A i₀) := by
  intro D E h
  have h₀ : (D : ι → Matrix m m ℂ) i₀ = (E : ι → Matrix m m ℂ) i₀ := congrArg Subtype.val h
  ext1
  funext v
  obtain ⟨p⟩ := hG.preconnected i₀ v
  rw [D.2.2.eq_conj_holonomy p, E.2.2.eq_conj_holonomy p, h₀]

/-- On a connected graph every twisted-fixed Hermitian matrix at `i₀` extends to an anti-parallel
section, by twisted transport along any walk from `i₀`. -/
theorem IsUnitaryConnection.evalAntiParallel_surjective [Fintype m] [DecidableEq m]
    (hA : IsUnitaryConnection G A) (hG : G.Connected) (i₀ : ι) :
    Function.Surjective (evalAntiParallel G A i₀) := by
  rintro ⟨X, hX⟩
  let w : ∀ v, G.Walk i₀ v := fun v => (hG.preconnected i₀ v).some
  let D : ι → Matrix m m ℂ := fun v =>
    (-1 : ℂ) ^ (w v).length • (holonomy A (w v) * X * (holonomy A (w v))ᴴ)
  have hherm : ∀ v, (D v).IsHermitian := fun v => by
    change ((-1 : ℂ) ^ (w v).length • (holonomy A (w v) * X * (holonomy A (w v))ᴴ)).IsHermitian
    refine isHermitian_neg_one_pow_smul ?_
    change (holonomy A (w v) * X * (holonomy A (w v))ᴴ)ᴴ = _
    rw [conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose, hX.1.eq,
      ← Matrix.mul_assoc]
  have hpar : IsAntiParallel G A D := by
    intro i j h
    change (-1 : ℂ) ^ (w i).length • (holonomy A (w i) * X * (holonomy A (w i))ᴴ) =
      -(A i j * D j * (A i j)ᴴ)
    rw [hA.twisted_conj_holonomy_eq hX (w i) ((w j).concat h.symm), holonomy_concat,
      Walk.length_concat, pow_succ]
    change _ = -(A i j * ((-1 : ℂ) ^ (w j).length •
      (holonomy A (w j) * X * (holonomy A (w j))ᴴ)) * (A i j)ᴴ)
    rw [conjTranspose_mul, Matrix.mul_smul, Matrix.smul_mul, mul_neg_one, neg_smul]
    simp only [Matrix.mul_assoc]
  refine ⟨⟨D, hherm, hpar⟩, Subtype.ext ?_⟩
  change (-1 : ℂ) ^ (w i₀).length • (holonomy A (w i₀) * X * (holonomy A (w i₀))ᴴ) = X
  rw [hA.twisted_conj_holonomy_eq hX (w i₀) Walk.nil, holonomy_nil, Walk.length_nil, pow_zero,
    one_smul, Matrix.one_mul, conjTranspose_one, Matrix.mul_one]

/-- **The twisted kernel (mirror of identity (3)).** On a connected graph, evaluation at a base
vertex `i₀` is an `ℝ`-linear equivalence between the Hermitian anti-parallel sections of a unitary
connection `A` (the zero set of the opposite energy of `diagonal D + A`) and the Hermitian
matrices fixed by the parity-twisted holonomy of every closed walk at `i₀`. -/
noncomputable def antiParallelSectionsEquivTwistedHolonomyFixed [Fintype m] [DecidableEq m]
    (hA : IsUnitaryConnection G A) (hG : G.Connected) (i₀ : ι) :
    antiParallelSections G A ≃ₗ[ℝ] twistedHolonomyFixed G A i₀ :=
  LinearEquiv.ofBijective (evalAntiParallel G A i₀)
    ⟨evalAntiParallel_injective hG i₀, hA.evalAntiParallel_surjective hG i₀⟩

@[simp]
theorem antiParallelSectionsEquivTwistedHolonomyFixed_apply_coe [Fintype m] [DecidableEq m]
    (hA : IsUnitaryConnection G A) (hG : G.Connected) (i₀ : ι) (D : antiParallelSections G A) :
    (antiParallelSectionsEquivTwistedHolonomyFixed hA hG i₀ D : Matrix m m ℂ) =
      (D : ι → Matrix m m ℂ) i₀ := rfl

end Twisted

section Bipartite

/-- **Bipartite graphs: the sign flip exchanges parallel and anti-parallel.** Let every edge of
`G` join `S` to its complement, and let `D'` agree with `D` on `S` and with `-D` off `S`. Then
`D'` is parallel iff `D` is anti-parallel. -/
theorem isParallel_iff_isAntiParallel_of_bipartite [Fintype m] {S : Set ι}
    (hS : ∀ i j, G.Adj i j → (i ∈ S ↔ j ∉ S)) {D D' : ι → Matrix m m ℂ}
    (h₁ : ∀ i ∈ S, D' i = D i) (h₂ : ∀ i ∉ S, D' i = -D i) :
    IsParallel G A D' ↔ IsAntiParallel G A D := by
  constructor
  · intro h i j hij
    by_cases hi : i ∈ S
    · have hj : j ∉ S := (hS i j hij).1 hi
      have e := h i j hij
      rw [h₁ i hi, h₂ j hj, Matrix.mul_neg, Matrix.neg_mul] at e
      exact e
    · have hj : j ∈ S := by
        by_contra hj
        exact hi ((hS i j hij).2 hj)
      have e := h i j hij
      rw [h₂ i hi, h₁ j hj] at e
      exact neg_eq_iff_eq_neg.1 e
  · intro h i j hij
    by_cases hi : i ∈ S
    · have hj : j ∉ S := (hS i j hij).1 hi
      rw [h₁ i hi, h₂ j hj, Matrix.mul_neg, Matrix.neg_mul]
      exact h i j hij
    · have hj : j ∈ S := by
        by_contra hj
        exact hi ((hS i j hij).2 hj)
      rw [h₂ i hi, h₁ j hj]
      exact neg_eq_iff_eq_neg.2 (h i j hij)

variable (S : Set ι) [DecidablePred (· ∈ S)]

/-- The sign flip of a section off the set `S`: `D i` on `S`, `-D i` off `S`. -/
noncomputable def signFlip (D : ι → Matrix m m ℂ) : ι → Matrix m m ℂ :=
  fun i => (if i ∈ S then (1 : ℝ) else -1) • D i

theorem signFlip_apply_of_mem (D : ι → Matrix m m ℂ) {i : ι} (hi : i ∈ S) :
    signFlip S D i = D i := by
  simp only [signFlip, hi, ↓reduceIte, one_smul]

theorem signFlip_apply_of_notMem (D : ι → Matrix m m ℂ) {i : ι} (hi : i ∉ S) :
    signFlip S D i = -D i := by
  simp only [signFlip, hi, ↓reduceIte, neg_one_smul]

theorem signFlip_signFlip (D : ι → Matrix m m ℂ) : signFlip S (signFlip S D) = D := by
  funext i
  simp only [signFlip, smul_smul]
  split_ifs <;> norm_num

theorem signFlip_add (D E : ι → Matrix m m ℂ) :
    signFlip S (D + E) = signFlip S D + signFlip S E := by
  funext i
  simp only [signFlip, Pi.add_apply, smul_add]

theorem signFlip_smul (c : ℝ) (D : ι → Matrix m m ℂ) :
    signFlip S (c • D) = c • signFlip S D := by
  funext i
  simp only [signFlip, Pi.smul_apply, smul_comm c]

theorem signFlip_isHermitian {D : ι → Matrix m m ℂ} (hD : ∀ i, (D i).IsHermitian) (i : ι) :
    (signFlip S D i).IsHermitian :=
  (hD i).smul (IsSelfAdjoint.all _)

variable (G A) in
/-- **Bipartite graphs: anti-parallel sections are parallel sections after the sign flip.** If
every edge of `G` joins `S` to its complement, the sign flip off `S` is an `ℝ`-linear
equivalence from the Hermitian anti-parallel sections onto the Hermitian parallel sections. -/
noncomputable def antiParallelSectionsEquivParallelSections [Fintype m]
    (hS : ∀ i j, G.Adj i j → (i ∈ S ↔ j ∉ S)) :
    antiParallelSections G A ≃ₗ[ℝ] parallelSections G A where
  toFun D := ⟨signFlip S D.1, signFlip_isHermitian S D.2.1,
    (isParallel_iff_isAntiParallel_of_bipartite hS
      (fun i hi => signFlip_apply_of_mem S D.1 hi)
      (fun i hi => signFlip_apply_of_notMem S D.1 hi)).2 D.2.2⟩
  invFun E := ⟨signFlip S E.1, signFlip_isHermitian S E.2.1,
    (isParallel_iff_isAntiParallel_of_bipartite hS
      (fun i hi => signFlip_apply_of_mem S (signFlip S E.1) hi)
      (fun i hi => signFlip_apply_of_notMem S (signFlip S E.1) hi)).1
      (by
        rw [signFlip_signFlip]
        exact E.2.2)⟩
  map_add' D E := Subtype.ext (signFlip_add S D.1 E.1)
  map_smul' c D := Subtype.ext (signFlip_smul S c D.1)
  left_inv D := Subtype.ext (signFlip_signFlip S D.1)
  right_inv E := Subtype.ext (signFlip_signFlip S E.1)

end Bipartite

end NonNormality
