import NonNormality
-- The scalar identity carries the weights `‖a i j‖²`; dropping them is false.
open Matrix NonNormality
open scoped Matrix.Norms.Frobenius
example {ι : Type*} [Fintype ι] [DecidableEq ι] (d : ι → ℝ) (a : Matrix ι ι ℂ) (ha : aᴴ = -a) :
    ‖(diagonal (fun i => (d i : ℂ)) + a) * (diagonal (fun i => (d i : ℂ)) + a)ᴴ -
        (diagonal (fun i => (d i : ℂ)) + a)ᴴ * (diagonal (fun i => (d i : ℂ)) + a)‖ ^ 2 =
      4 * ∑ i, ∑ j, (d i - d j) ^ 2 := by
  rw [norm_sq_selfCommutator_scalar d a ha]
  congr 1
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring_nf
