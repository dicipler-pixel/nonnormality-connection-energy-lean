import NonNormality

/-!
Negations of the four false controls of version 11 (compiled with warnings as errors).

Each false control in `FalseControls/` is a statement that must fail to compile. The theorems
below prove that the statement is actually false, by a concrete counterexample, so that a control
can never be "rejected" merely because its proof attempt was weak.

* `not_constant_shift_two_cA`: `FalseControls/constant_shift_two_cA_wrong.lean`.
* `not_duality_without_third_leg`: `FalseControls/duality_without_third_leg_wrong.lean`.
* `not_projector_budget_two_k`: `FalseControls/projector_budget_two_k_wrong.lean`.
* `not_double_cover_missing_factor_two`:
  `FalseControls/double_cover_missing_factor_two_wrong.lean`.
-/

open Matrix NonNormality
open scoped Matrix.Norms.Frobenius

/-- The shift by `c • 1` moves `H * H - Hᴴ * Hᴴ` by `(4 * c) • A`, not `(2 * c) • A`: with
`D = 0`, `A = !![0, 1; -1, 0]` (`1 × 1` blocks) and `c = 1` the `(2 * c) • A` formula would force
`4 = 2`. -/
theorem not_constant_shift_two_cA :
    ¬ ∀ (D : Fin 2 → Matrix (Fin 1) (Fin 1) ℂ), (∀ i, (D i).IsHermitian) →
      ∀ (A : Matrix (Fin 2) (Fin 2) (Matrix (Fin 1) (Fin 1) ℂ)), Aᴴ = -A → ∀ c : ℝ,
      (diagonal D + A + c • 1) * (diagonal D + A + c • 1) -
          (diagonal D + A + c • 1)ᴴ * (diagonal D + A + c • 1)ᴴ =
        ((diagonal D + A) * (diagonal D + A) - (diagonal D + A)ᴴ * (diagonal D + A)ᴴ) +
          (2 * c) • A := by
  intro h
  have hA : (!![0, 1; -1, 0] : Matrix (Fin 2) (Fin 2) (Matrix (Fin 1) (Fin 1) ℂ))ᴴ =
      -!![0, 1; -1, 0] := by
    refine Matrix.ext fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp [conjTranspose_apply]
  have h1 := h 0 (fun _ => isHermitian_zero) _ hA 1
  rw [mul_self_sub_conjTranspose_mul_self_diagonal_add_smul_one 0 (fun _ => isHermitian_zero) _
    hA 1, add_right_inj] at h1
  have h2 := congrFun (congrFun (congrFun (congrFun h1 0) 1) 0) 0
  norm_num [Matrix.smul_apply] at h2

/-- `P² + V² = 1` fails without the third leg: for `a = !![1, 0; 0, 0]`, `b = !![0, 0; 0, 1]`
one has `P = V = 0` and `L² = 1`. -/
theorem not_duality_without_third_leg :
    ¬ ∀ (a b : Matrix (Fin 2) (Fin 2) ℂ), a.IsHermitian → b.IsHermitian →
      ‖a‖ ^ 2 + ‖b‖ ^ 2 ≠ 0 →
      ((‖a‖ ^ 2 - ‖b‖ ^ 2) / (‖a‖ ^ 2 + ‖b‖ ^ 2)) ^ 2 +
        ((‖a + b‖ ^ 2 - ‖a - b‖ ^ 2) / (‖a + b‖ ^ 2 + ‖a - b‖ ^ 2)) ^ 2 = 1 := by
  intro h
  have ha : (!![1, 0; 0, 0] : Matrix (Fin 2) (Fin 2) ℂ).IsHermitian := by
    refine Matrix.IsHermitian.ext fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp
  have hb : (!![0, 0; 0, 1] : Matrix (Fin 2) (Fin 2) ℂ).IsHermitian := by
    refine Matrix.IsHermitian.ext fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp
  have hna : ‖(!![1, 0; 0, 0] : Matrix (Fin 2) (Fin 2) ℂ)‖ ^ 2 = 1 := by
    rw [frobenius_norm_sq]
    simp [Fin.sum_univ_two]
  have hnb : ‖(!![0, 0; 0, 1] : Matrix (Fin 2) (Fin 2) ℂ)‖ ^ 2 = 1 := by
    rw [frobenius_norm_sq]
    simp [Fin.sum_univ_two]
  have hg : frobeniusInner (!![1, 0; 0, 0] : Matrix (Fin 2) (Fin 2) ℂ) !![0, 0; 0, 1] = 0 := by
    simp [frobeniusInner, Matrix.trace, Matrix.mul_apply, Fin.sum_univ_two, conjTranspose_apply]
  have hs : ‖(!![1, 0; 0, 0] : Matrix (Fin 2) (Fin 2) ℂ)‖ ^ 2 +
      ‖(!![0, 0; 0, 1] : Matrix (Fin 2) (Fin 2) ℂ)‖ ^ 2 ≠ 0 := by
    rw [hna, hnb]
    norm_num
  have h1 := h _ _ ha hb hs
  have h2 := duality_sum_sq _ _ hs
  rw [hna, hnb] at h1
  rw [hna, hnb, hg] at h2
  have h3 : (4 * (1 * 1 - (0 : ℝ) ^ 2) / (1 + 1) ^ 2 : ℝ) = 0 := by
    linear_combination h2 - h1
  norm_num at h3

/-- `‖P - R‖² + ‖P + R‖² = 2 k` fails: for `P = R = 1` on `ℂ¹` (so `k = 1`) the true value is
`4`. -/
theorem not_projector_budget_two_k :
    ¬ ∀ (P R : Matrix (Fin 1) (Fin 1) ℂ), P.IsHermitian → P * P = P → R.IsHermitian →
      R * R = R → ∀ k : ℝ, trace P = k → trace R = k →
      ‖P - R‖ ^ 2 + ‖P + R‖ ^ 2 = 2 * k := by
  intro h
  have h1 : trace (1 : Matrix (Fin 1) (Fin 1) ℂ) = ((1 : ℝ) : ℂ) := by simp
  have h2 := h 1 1 isHermitian_one (one_mul 1) isHermitian_one (one_mul 1) 1 h1 h1
  have h3 := norm_sub_sq_add_norm_add_sq_of_projector isHermitian_one (one_mul 1)
    isHermitian_one (one_mul 1) h1 h1
  linarith

/-- The double-cover energy is `2 E₋(S) + 2 E₊(T)`, not `E₋(S) + E₊(T)`: on the single edge
`0 — 1` with `A 0 1 = 1`, `S = 0`, `T = 1` the opposite energy of `T` is `4 ≠ 0`. -/
theorem not_double_cover_missing_factor_two :
    ¬ ∀ {ι m : Type} [Fintype ι] [DecidableEq ι] [Fintype m] [DecidableEq m]
      {G : SimpleGraph ι} [DecidableRel G.Adj] {A : Matrix ι ι (Matrix m m ℂ)},
      IsUnitaryConnection G A → ∀ S T : ι → Matrix m m ℂ,
      connectionEnergy (doubleCover G) (liftConnection A) (coverField S T) =
        connectionEnergy G A S + oppositeEnergy G A T := by
  intro h
  have hA : IsUnitaryConnection (⊤ : SimpleGraph (Fin 2))
      (!![0, 1; -1, 0] : Matrix (Fin 2) (Fin 2) (Matrix (Fin 1) (Fin 1) ℂ)) where
    conjTranspose_eq_neg := by
      refine Matrix.ext fun i j => ?_
      fin_cases i <;> fin_cases j <;> simp [conjTranspose_apply]
    eq_zero_of_not_adj := by
      intro i j hij
      rw [SimpleGraph.top_adj, not_not] at hij
      subst hij
      fin_cases i <;> rfl
    mem_unitaryGroup := by
      intro i j hij
      rw [SimpleGraph.top_adj] at hij
      fin_cases i <;> fin_cases j
      · exact absurd rfl hij
      · change (1 : Matrix (Fin 1) (Fin 1) ℂ) ∈ unitaryGroup (Fin 1) ℂ
        exact one_mem _
      · change (-1 : Matrix (Fin 1) (Fin 1) ℂ) ∈ unitaryGroup (Fin 1) ℂ
        rw [mem_unitaryGroup_iff, star_neg, star_one, neg_mul_neg, one_mul]
      · exact absurd rfl hij
  have h1 := h hA 0 (fun _ => 1)
  rw [connectionEnergy_doubleCover hA 0 (fun _ => 1)] at h1
  have hS : connectionEnergy (⊤ : SimpleGraph (Fin 2)) !![0, 1; -1, 0]
      (0 : Fin 2 → Matrix (Fin 1) (Fin 1) ℂ) = 0 :=
    (connectionEnergy_eq_zero_iff _ _).2 fun i j _ => by simp
  have hT : oppositeEnergy (⊤ : SimpleGraph (Fin 2)) !![0, 1; -1, 0]
      (fun _ => (1 : Matrix (Fin 1) (Fin 1) ℂ)) ≠ 0 := by
    intro h0
    have e := (oppositeEnergy_eq_zero_iff _ _).1 h0 0 1 (by simp)
    change (1 : Matrix (Fin 1) (Fin 1) ℂ) =
      -((1 : Matrix (Fin 1) (Fin 1) ℂ) * 1 * (1 : Matrix (Fin 1) (Fin 1) ℂ)ᴴ) at e
    rw [Matrix.one_mul, conjTranspose_one, Matrix.one_mul] at e
    have e0 := congrFun (congrFun e 0) 0
    norm_num at e0
  apply hT
  linarith
