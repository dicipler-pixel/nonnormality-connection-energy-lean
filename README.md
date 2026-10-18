# Non-normality is connection energy — Lean 4 formalization

Lean 4 / Mathlib formalization of

> Jeromie Beasley, *Non-normality is connection energy*, 17 September 2026,
> Zenodo record 22804072 (v7).

Every mathematical statement of the paper is proved, with no `sorry`, no warnings and only the
three standard axioms (`propext`, `Classical.choice`, `Quot.sound`).

## Setting

`G : SimpleGraph ι` is a finite graph, `m` a finite type (the fibre `ℂ^r`). An operator
`H = diagonal D + A : Matrix ι ι (Matrix m m ℂ)` has Hermitian diagonal blocks `D i` and a
**unitary connection** `A` (`IsUnitaryConnection G A`): `Aᴴ = -A`, `A i j = 0` off the edges,
`A i j` unitary on the edges. Frobenius norms throughout (`open scoped Matrix.Norms.Frobenius`).

## Main theorems (namespace `NonNormality`)

```lean
-- Identity (1): self-commutator energy = connection energy
theorem norm_sq_selfCommutator_div_eight (hA : IsUnitaryConnection G A)
    (hD : ∀ i, (D i).IsHermitian) :
    ‖(diagonal D + A) * (diagonal D + A)ᴴ - (diagonal D + A)ᴴ * (diagonal D + A)‖ ^ 2 / 8 =
      connectionEnergy G A D
-- where connectionEnergy G A D
--   = (∑ i, ∑ j, if G.Adj i j then ‖D i - A i j * D j * (A i j)ᴴ‖ ^ 2 else 0) / 2
-- (= the sum over edges; edge form: norm_sq_selfCommutator_div_eight_eq_sum_edgeFinset;
--  flattened (ι × m)-matrix form: norm_sq_selfCommutator_comp_div_eight)

-- Identity (2): normal ⇔ parallel
theorem isStarNormal_iff_isParallel (hA : IsUnitaryConnection G A)
    (hD : ∀ i, (D i).IsHermitian) :
    IsStarNormal (diagonal D + A) ↔ ∀ i j, G.Adj i j → D i = A i j * D j * (A i j)ᴴ

-- Identity (3): on a connected graph, parallel Hermitian sections ≅ holonomy-fixed matrices
noncomputable def parallelSectionsEquivHolonomyFixed (hA : IsUnitaryConnection G A)
    (hG : G.Connected) (i₀ : ι) : parallelSections G A ≃ₗ[ℝ] holonomyFixed G A i₀
-- holonomyFixed G A i₀ = {X | X.IsHermitian ∧ ∀ p : G.Walk i₀ i₀,
--                               holonomy A p * X * (holonomy A p)ᴴ = X}
--   (equivalently Commute X (holonomy A p): mem_holonomyFixed_iff_commute)

-- General form, no unitarity, and the scalar (weighted Dirichlet) case
theorem norm_sq_selfCommutator_eq (hD) (hA : Aᴴ = -A) :
    ‖[H, Hᴴ]‖ ^ 2 = 4 * ∑ i, ∑ j, ‖D i * A i j - A i j * D j‖ ^ 2
theorem norm_sq_selfCommutator_scalar (d : ι → ℝ) (a : Matrix ι ι ℂ) (ha : aᴴ = -a) :
    ‖[H, Hᴴ]‖ ^ 2 = 4 * ∑ i, ∑ j, ‖a i j‖ ^ 2 * (d i - d j) ^ 2
```

## Files

| File | Content |
|---|---|
| `NonNormality/Frobenius.lean` | `‖A‖² = ∑‖Aᵢⱼ‖²`, `‖A‖² = re tr(AᴴA)`, unitary invariance of the Frobenius norm |
| `NonNormality/SelfCommutator.lean` | identities (1), (2), general and scalar forms, edge-sum lemma |
| `NonNormality/Holonomy.lean` | walk holonomy, transport, identity (3) |
| `NonNormality/Flatten.lean` | `Matrix.comp` commutes with `ᴴ`, preserves the Frobenius norm; (1), (2) for the flattened matrix |
| `NonNormality/SymSkew.lean` | (findings-v2) symmetric + skew: `[S+εK,(S+εK)*] = 2ε[K,S]`, normal ⇔ commute |
| `NonNormality/Lattice.lean` | (findings-v2) `J`, `MJ+JM = tr M • J`, symmetric lattice transport `Δ₁ ⊗ J`, SO(2) gauge |
| `NonNormality/Kernel.lean` | (findings-v2) non-unitary normality criterion (v1), rank-one channel, kernel dimension |
| `NonNormality/Evenness.lean` | (findings-v2) ε ↦ −ε evenness, first-order cancellation, positive second-order 2×2 model |
| `NonNormality/QGT.lean` | (findings-v2) quantum geometric tensor, `Q = g + (i/2)Ω`, metric–curvature inequality, tangent vectors |
| `NonNormality/Localization.lean` | (findings-v2) participation / localization index bounds |
| `NonNormality/Counterexamples.lean` | (findings-v2) Lean counterexamples to statements in the earlier papers |
| `FINDINGS_INVENTORY.md` | (findings-v2) every finding from the original papers, tagged, with source and page |
| `numerics/check_findings.py` | (findings-v2) numpy checks of the findings (output `check_findings_output.txt`) |
| `originals/` | (findings-v2) copies of the source PDFs and figures |
| `checks/Necessity.lean` | proves Hermitian `D` is necessary (normal but non-parallel example) |
| `FalseControls/` | 10 false statements that must fail to compile |
| `scripts/check_all.py` | runs every check, writes `verification/report.json` |
| `STATEMENTS.md` | every statement of the paper, classified, with remarks |
| `MATHLIB_FIT.md` | what could go to Mathlib, names, placement, verdict |

## Build and check

Lean `v4.34.1`, Mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612` (tag `v4.34.1`, pinned in
`lake-manifest.json`).

```
lake build
python3 scripts/check_all.py
```

## License

Code: MIT OR Apache-2.0 (see `LICENSE`). Copyright (c) 2026 Jeromie Beasley.
