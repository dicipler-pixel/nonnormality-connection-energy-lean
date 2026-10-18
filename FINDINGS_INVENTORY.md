# FINDINGS INVENTORY: every way we saw "non-normality is connection energy" work

Branch `findings-v2` (off main `dccb784`). Author: Jeromie Beasley. License: MIT OR Apache-2.0.

This file lists every claim, method, route, example and numerical observation found in the
original material behind *Non-Normality Is Connection Energy* (Zenodo 22804072, v1–v7), and
says where each one now lives.

**Page numbers** are physical PDF pages, counted with `pdftotext` form feeds.

**Numerics** are in `numerics/check_findings.py`, with output in
`numerics/check_findings_output.txt`. The script uses numpy only, seed 20261018. Section tags
(L1, C1, Q1, …) refer to that script.

## Tags

| Tag | Meaning |
|---|---|
| **IN REPO** | Proved in Lean. The Lean name is given. Zero sorry; only the standard axioms (`propext`, `Classical.choice`, `Quot.sound`). |
| **FORMALIZABLE NOW** | A precise finite-dimensional statement that Mathlib can express today. Not yet done, usually because the proof is long. |
| **NEEDS MISSING MATHLIB** | Needs analysis that Mathlib does not have yet. |
| **INTERPRETIVE** | Physical, heuristic or narrative reading. Not a theorem. |
| **ERROR** | The original statement is false or misstated. A numerical and/or Lean counterexample is given. |

## Sources

Copies of all sources are in `originals/`.

| Key | File | Pages | Notes |
|---|---|---|---|
| v1–v7 | `nonnormality_is_connection_energy_v1..v7.pdf` (acc-research September_downloads) | 2 / 1 | Zenodo 22804072 drafts. v7 is the formalized main paper. |
| DIR | dirichlet note (September_downloads) | 2 | Scalar case: Fiedler, rank-one, arg/constant. |
| 50b1 | `originals/2026-06-18_Spectral_and_Pseudospectral_Properties_17pp_50b1aadc.pdf` | 17 | Lattice engine H_N(ε)=A+D₀+εE. |
| 48b2 | `originals/2026-06-18_…_20pp_with_figures_48b2b086.pdf` | 20 | Same, plus figures, QGT and LPI. |
| e0c9 | `originals/2026-06-22_NonNormal_Lattice_Transport_Operators_18pp_e0c914f8.pdf` | 18 | |
| 69c4 | `originals/2026-06-22_NonNormal_Lattice_Transport_Operators_20pp_69c4950c.pdf` | 20 | Adds QGT and Dunford. |
| 723a | `originals/2026-06-24_Spectral_Stability_Across_Obstruction_Interfaces_25pp_723ab87b.pdf` | 25 | Interfaces, gauge, Kreiss, E_avg appendix. |
| 81cd | `originals/2026-06-29_Directional_Transport_Geometry_of_Admissible_Channels_63pp_81cddb54.pdf` | 63 | Zenodo 21089303/21089304. Already on Drive (same bytes). |
| FIL | `Filament_Operator_Research_Revision_4.pdf` (October_downloads) | 11 | Zenodo 22959175. Jordan-block growth. Already on Drive. |
| FIG1–4 | `originals/figure_{6fadf476,6f06cf1e,de7dd595,e9195122}.png` | | 6f06cf1e: sector tree A / D₀ / εE. e9195122: "Integrated Quadralogy Architecture Map". |
| LEDGER | `/workspace/dl2/md/…DIRAC_TIME_UNIFIED_INTAKE_AND_CLAIM_LEDGER_20260919.md.txt` | | Earlier review of 22804072. Its verdicts were: proof correct; "do not identify the skew A with the symmetric periodic-gluing A". |

The explainer mp4 was not watched, as instructed, and no sidecar text exists for it.

---

## 1. Core identity and kernel (v1–v7, DIR)

| # | Finding | Source | Tag | Lean / note |
|---|---|---|---|---|
| K1 | [H,H*] = −2[D,A] for H = D+A, D Hermitian block-diagonal, A skew | v7, v1 p1 | IN REPO | `selfCommutator_diagonal_add` |
| K2 | ⅛‖[H,H*]‖² = Σ_edges ‖D_i − A_ij D_j A_ij*‖² | v7 (1) | IN REPO | `norm_sq_selfCommutator_div_eight`, `…_eq_sum_edgeFinset`, `norm_sq_selfCommutator_comp_div_eight` |
| K3 | Normal ⟺ D parallel | v7 (2) | IN REPO | `isStarNormal_iff_isParallel`, `isStarNormal_comp_iff_isParallel` |
| K4 | ker E_A ≅ Fix_Herm(Hol) | v7 (3) | IN REPO | `parallelSectionsEquivHolonomyFixed` |
| K5 | Dimension of the kernel = dimension of Fix | v7 | IN REPO (new) | `finrank_parallelSections_eq` |
| K6 | General **non-unitary** edges: H normal ⟺ D_i A_ij = A_ij D_j for all i,j. Unitarity not needed. | v1 p1 (dropped in v2+) | IN REPO (new) | `isStarNormal_diagonal_add_iff`, `isStarNormal_diagonal_add_scalar_iff`; numerics C2 |
| K7 | Weighted Dirichlet scalar form | v7, DIR p1 | IN REPO | `norm_sq_selfCommutator_scalar` |
| K8 | Rank-one aligned channel: D·(uvᵀ) − (uvᵀ)·D is rank one; energy = channel mismatch | DIR p1 | IN REPO (new) | `mul_vecMulVec_sub_vecMulVec_mul`; numerics C4 |
| K9 | Orientation independence of the edge summand | v2 remark | IN REPO | `IsUnitaryConnection.norm_sub_conj_comm` |
| K10 | Holonomy reversal sign | v3 | IN REPO | `IsUnitaryConnection.holonomy_reverse` (false control `holonomy_reverse_no_sign_wrong`) |
| K11 | 4-cycle, r=3: kernel dimensions 3 / 5 / 9 (generic / partial / trivial holonomy) | v1 p2 | FORMALIZABLE NOW (numerics C1 confirm) | Needs explicit finrank computations on a concrete 4-cycle. Long but routine. |
| K12 | Fiedler bound E ≥ λ₂(L_w)·‖D − mean‖² (scalar) | v1 p2, DIR p1 | NEEDS MISSING MATHLIB | Needs λ₂ variational characterization (Courant–Fischer) for weighted Laplacians. Numerics C3 confirm. |
| K13 | arg/constant gauge: scalar kernel = constants on connected G | DIR p1 | IN REPO (via K4 with r=1) | |
| K14 | Singer–Wu / synchronization reading; Bandeira–Singer–Spielman references | v1 p1–2 (dropped) | INTERPRETIVE | Connection Laplacian analogy. |
| K15 | "Ladder" of generalizations (scalar → U(1) → U(r)) | v1 p1–2 (dropped) | INTERPRETIVE | All rungs are covered by K2–K7. |
| K16 | U_ij(X)=A_ij X A_ij*; Kobayashi–Nomizu holonomy reading | v3 | IN REPO (as `IsParallel`) / INTERPRETIVE | |

## 2. Symmetric + skew decomposition (50b1, 48b2, e0c9, 69c4, 723a)

| # | Finding | Source | Tag | Lean / note |
|---|---|---|---|---|
| S1 | [S+K, (S+K)*] = 2[K,S] when S=S*, K=−K* | 50b1, 723a p10 | IN REPO (new) | `selfCommutator_add_smul_of_skew`, `selfCommutator_add`, `selfCommutator_add_smul` |
| S2 | S+εK normal ⟺ [S,K]=0 (ε≠0) | 50b1, 48b2 | IN REPO (new) | `isStarNormal_add_iff_commute`, `isStarNormal_add_smul_iff_commute`, `isStarNormal_iff_commute_add_sub` |
| S3 | ‖[H,H*]‖ = 2|ε|‖[K,S]‖ | 723a p11 | IN REPO (new) | `norm_selfCommutator_add_smul_of_skew` |
| S4 | Exact expansion [H,Hᵀ] = ε[E−Eᵀ,S] + ε²[E,Eᵀ]; no ε² term when E is skew | 50b1, 723a p11–12 | numerics L2 confirm; algebra covered by S1 | |
| S5 | A = α(Δ₁ ⊗ J) is symmetric; spectrum ∓2α sin(2πk/N) | 723a p10, 48b2 p10, 69c4 p9 | Symmetry IN REPO (new): `kronecker_transpose_of_skew`, `centralDiff_transpose`, `latticeTransport_transpose`. Spectrum: FORMALIZABLE NOW (needs a DFT diagonalization; heavy). Numerics L1 confirm. | |
| S6 | MJ+JM = tr(M)·J for any 2×2 M | 723a p19 §10.4 | IN REPO (new) | `mul_symplecticJ_add`, `mul_symplecticJ_add_of_trace_eq_zero`, `transpose_mul_symplecticJ`, `transpose_mul_symplecticJ_of_trace_eq_zero`, `transpose_mul_symplecticJ_sub` |
| S7 | J facts: Jᵀ=−J, J²=−1 | all | IN REPO (new) | `symplecticJ_transpose`, `symplecticJ_mul_self` |
| S8 | Constant SO(2) rotation is a similarity of the lattice operator; a reflection flips J | 723a p19, 81cd Prop 5 p48 | IN REPO (new) | `rot`, `rot_transpose_mul_self`, `rot_mul_symplecticJ_mul_transpose`, `reflect_mul_symplecticJ_mul_transpose`, `kronecker_one_rot_conj_latticeTransport`, `kronecker_one_rot_transpose_mul_self` |
| S9 | First-order cancellation: d/dε of det / log det / Tr resolvent at 0 vanish (ε ↦ −ε symmetry via transpose) | 81cd Prop 2 p33 | IN REPO (new) | `transpose_add_smul_of_symm_skew`, `det_add_smul_neg`, `trace_inv_sub_add_smul_neg`, `deriv_zero_of_even`, `deriv_det_add_smul_zero`, `deriv_log_det_add_smul_zero`, `deriv_trace_inv_sub_add_smul_zero`, `trace_mul_eq_zero_of_symm_skew` |
| S10 | Second-order sign (2×2 model): det(diag(a,b)+εkJ) = ab+ε²k² > ab, so log det increases | 81cd Lemma 5 p34 (correct) vs Thm 8 p35 (wrong sign) | IN REPO (new) | `det_diag_add_smul_skew_two`, `log_det_diag_add_smul_skew_two_gt` (false control `log_det_negative_correction_wrong`). The general-n statement det(S+K) ≥ det S for S≻0 is FORMALIZABLE NOW (det(I+S^{-½}KS^{-½}) = Π(1+μ²) argument; heavy). |
| S11 | Exceptional points need a non-diagonalizable case; the Jordan block is not diagonalizable | 81cd Thm 3 p13 | IN REPO (new) | `not_diagonalizable_jordan` (shows K=0 / Jordan direction of the "iff" fails) |

## 3. Geometry: QGT, curvature, projectors (48b2, 69c4, 81cd, FIG4)

| # | Finding | Source | Tag | Lean / note |
|---|---|---|---|---|
| Q1 | Q(V,W)=Tr(ΠVW), g=Re Q, Ω=−i Tr(Π[V,W]) is real, Q = g + (i/2)Ω | 81cd p33 §12, 69c4 p16–20, 48b2 p17/20 | IN REPO (new) | `qgt`, `qgtMetric`, `qgtCurvature`, `qgt_swap`, `neg_I_mul_trace_commutator`, `qgtCurvature_eq`, `qgt_eq_metric_add_curvature`, `qgt_eq_trace_conjTranspose_mul` |
| Q2 | g(V,V) ≥ 0; |Q(V,W)|² ≤ g(V,V)g(W,W); |Ω(V,W)| ≤ 2√(g(V,V)g(W,W)) | 81cd §12.6 | IN REPO (new) | `re_trace_conjTranspose_mul_self_nonneg`, `qgtMetric_self_nonneg`, `norm_sq_trace_conjTranspose_mul_le`, `norm_sq_qgt_le`, `abs_qgtCurvature_le` |
| Q3 | Tangent vectors V = ΠV(1−Π)+(1−Π)VΠ: complementary projector gives the same g, opposite Ω; g(V,V) = ½Tr(V²) | 81cd §12.6, FIG4 | IN REPO (new) | `IsTangent`, `IsTangent.mul_mul_self`, `IsTangent.one_sub_mul_mul_one_sub`, `trace_one_sub_mul_mul_of_isTangent`, `qgt_one_sub_of_isTangent`, `qgtMetric_one_sub_of_isTangent`, `qgtCurvature_one_sub_of_isTangent`, `qgtMetric_self_of_isTangent` |
| Q4 | Two-band saturation |Ω| = 2g for rank-1 in ℂ² | 81cd §12.6.1 | FORMALIZABLE NOW (numerics Q1: error 4e-15) | Explicit 2×2 computation. |
| Q5 | Tr(Π₁Π₂) = Σ cos²θ_k (principal angles) | 81cd p46–47 | NEEDS MISSING MATHLIB | No principal-angle / CS decomposition in Mathlib. Numerics confirm. |
| Q6 | Riesz projector Π = (2πi)⁻¹∮(z−H)⁻¹dz; Dunford trace-log; Kato stability | 69c4 p13–16, 723a p16, p22 | NEEDS MISSING MATHLIB | Contour holomorphic functional calculus for matrices is not in Mathlib. NB: FIL §7 itself notes the non-normal Riesz projector is not orthogonal, so FIG4's "Π_k ∈ Gr(k,H)" needs Π orthogonalized first. |
| Q7 | Localization / participation index LPI ∈ [1/N, 1] | 48b2 p5/12/17, 723a p23 | IN REPO (new) | `participationIndex`, `one_le_card_mul_sum_sq`, `sum_sq_le_one`, `inv_card_le_participationIndex`, `participationIndex_le_one`, `localizationIndex`, `localizationIndex_eq`, `inv_card_le_localizationIndex`, `localizationIndex_le_one`; numerics Q2 |
| Q8 | Z_A = log det_ζ(H_eff), Mellin inversion | FIG4, 69c4 | NEEDS MISSING MATHLIB | Zeta-regularized determinants are not in Mathlib. |

## 4. Pseudospectra, growth, continuum (50b1, 48b2, 723a, 81cd, FIL)

| # | Finding | Source | Tag | Lean / note |
|---|---|---|---|---|
| P1 | Pseudospectral bulge, Bauer–Fike bound | 723a p1/15/22, 48b2 p14 | NEEDS MISSING MATHLIB (pseudospectra / Bauer–Fike not in Mathlib) | Numerics L6: height − η is O(ε), contradicting the paper's √(εΔ) (ERROR E4). |
| P2 | Kreiss constant / transient growth | 723a p15, 48b2 p1–14, 81cd Thm 15 p52 | NEEDS MISSING MATHLIB | ERROR E5 below. |
| P3 | Filament Thm 4.1: ‖e^{−Jt}‖ = e^{−bt}(√(4+μ²t²)+μt)/2 for J = [[b,μ],[0,b]]; growth ⟺ κ=μ/b > 2; t*, M_max; κ_r = 2.48526751266, x = 0.79681213002 | FIL Thm 4.1 | FORMALIZABLE NOW (2×2 singular values of an explicit exponential; long) | Numerics F1 confirm to 1e-10. |
| P4 | Filament Thm 2.1: invariant span{e2,e5}, char poly (λ−b)²−μγ | FIL Thm 2.1 | FORMALIZABLE NOW | Explicit 5×5 charpoly. |
| P5 | Filament Prop 5.1: sin θ_δ linear in δ vs √(γ/μ) | FIL Prop 5.1 | FORMALIZABLE NOW (2×2 eigenvector angle) | |
| P6 | Continuum limit: second difference → ψ'' with error ≤ δ²‖ψ''''‖/12 | 723a p21, 81cd p53 Thm 16 | FORMALIZABLE NOW (Taylor with remainder is in Mathlib); operator convergence only strong (ERROR E10) | Numerics X1 confirm. |
| P7 | Interface Schur complement resolvent | 723a Thm 10.3 | FORMALIZABLE NOW once the sign is fixed (ERROR E9) | |
| P8 | Gluing resolvent bound | 723a, 81cd | FORMALIZABLE NOW (heavy) | |
| P9 | Degree / cascade Thm 3.3; Kakeya Hausdorff-dimension bound (81cd Thm 4 p31) | 723a, 81cd | NEEDS MISSING MATHLIB (and Thm 4 is stated without proof) | |

## 5. Interpretive material (not theorems)

These are all INTERPRETIVE:

- inertia tensor and Θ_n
- Dzhanibekov effect (723a p18)
- Orr–Sommerfeld analogy
- shape sphere
- refraction law and directional filtering (81cd)
- Dirac and spin-1 models (81cd p47)
- colour space / Bezold–Brücke / THz (FIG4)
- "transport / obstruction / non-normality sector" tree (FIG2)
- Singer–Wu synchronization reading

They are kept here so that nothing is lost.

---

## 6. Errors found in the originals

Each error has a numerical check and/or a Lean counterexample. The Lean counterexamples are
in `NonNormality/Counterexamples.lean`; false controls are in `FalseControls/`.

| # | Original claim | Correct statement | Evidence |
|---|---|---|---|
| E1 | 723a §10.4 p19: "MJ+JM = [[2b, d−a],[d−a, −2b]]" | That matrix is JM−MJ (and it is symmetric). The true anticommutator is tr(M)·J, so E_lead sees only trace gradients of B_n. | `paperBlock_eq_symplecticJ_mul_sub`, `paperBlock_ne_anticommutator`, `mul_symplecticJ_add`; numerics L3; false control `anticommutator_paper_block_wrong` |
| E2 | 723a App. A p24–25: E = E_lead + E_avg carries the Δ_n anisotropy; E_avg is O(ε²) | The skew part of E_avg is (tr δB/2)·J. Trace-constant anisotropic B_n give a **symmetric** H (no non-normality at all). E_avg enters at O(ε): the ratio is the constant 1.1121. | numerics L4; S6 lemmas |
| E3 | 48b2 p8/10, 69c4 p12, 723a p10: "eigenvalues remain on the real axis" | False. max |Im λ| ≈ 2.62 ε. | numerics L5; `not_real_eigenvector_smul_add_symplecticJ`; false control `eigenvalues_stay_real_wrong` |
| E4 | Bulge height ∼ √(εΔ) (723a p1/15/22, 48b2 p14) | Excess height is O(ε): (h−η)/ε ≈ 2.63 is constant, as Bauer–Fike predicts. | numerics L6 |
| E5 | Kreiss bound with 1/√ε growth; "equivalent formulations" (723a p15, 81cd Thm 15) | The RHP Kreiss constant is infinite (max Re λ > 0). The distance-based version is bounded by cond(V), which stays bounded. The formulations are not equivalent. | numerics L7 |
| E6 | GL(2) gauge invariance B_n ↦ U_n B_n U_nᵀ with A fixed (723a p19, 81cd Prop 5) | False for GL(2), and false for **local** SO(2) (spectrum changes by 0.311). Only a constant SO(2) rotation is a similarity; a reflection flips J. | `trace_gl_conj_ne`, S8 lemmas; numerics L8; false control `gl2_gauge_wrong` |
| E7 | FIG4 / 48b2 / 69c4: "Q_Π = g_Π + iΩ_Π" | Q = g + (i/2)Ω (81cd p33 itself uses i/2). Also, g(V,V) = ½Tr(V²) holds only for tangent V. | `qgt_eq_metric_add_curvature`, `qgt_ne_metric_add_I_mul_curvature`, `qgtMetric_self_of_isTangent`; false control `qgt_g_plus_i_omega_wrong` |
| E8 | 81cd Thm 8 p35: the ε² correction is negative with gap² denominators | It is +½Σ|K_ij|²/(λ_iλ_j) > 0 (log det increases). Lemma 5 p34 is correct. | `log_det_diag_add_smul_skew_two_gt`; numerics T1; false control `log_det_negative_correction_wrong` |
| E9 | 723a Thm 10.3 Schur complement | Should be zI − H_A − C R_B C* (sign). | algebra check |
| E10 | Continuum limit "in norm" (723a p21, 81cd Thm 16) | Only strong (pointwise on smooth ψ) convergence. Δ_n is undefined if λ_min ≤ 0. | numerics X1 |
| E11 | 81cd Thm 3 p13: EP ⟺ coalescence AND non-normal K | Fails both ways. K = 0 at a Jordan block is an EP with normal K. K = [[1,0,1],[0,1,0],[0,0,2]] is coalesced and non-normal, yet diagonalizable. | `not_diagonalizable_jordan`; numerics T2 |
| E12 | 81cd Lemma 10 p36: rigidity R ≥ 1/m + O(ε²) | Fails at δB = 0: R = 1/(m+ε) < 1/m. | `rigidity_lt_of_zero_gradient`; numerics T3 |
| E13 | Identifying the skew connection A with the symmetric periodic-gluing A (LEDGER) | These are different operators. The v7 A is skew; the lattice A = α(Δ₁⊗J) is symmetric. | kept separate in the repo (`latticeTransport` vs `IsUnitaryConnection`) |

## 7. What was dropped between versions of 22804072

| From → to | Dropped / changed | Where it is now |
|---|---|---|
| v1 → v2 | General non-unitary summand; invertible-A kernel corollary | K6 (`isStarNormal_diagonal_add_iff`) |
| v1 → v2 | Singer–Wu reading; "ladder"; references (Bandeira–Singer–Spielman, …) | K14, K15 (interpretive) |
| v1 → v2 | Fiedler bound; 4-cycle example (dims 3/5/9) | K12 (needs Mathlib), K11 (formalizable; numerics) |
| v2 → v3 | Orientation remark | K9 (in repo) |
| v3 → v4 | U_ij notation; Kobayashi–Nomizu | K16 |
| v4 → v5 | Comm(Hol) → Fix_Herm(Hol) | K4 (Fix form, in repo) |
| v6 → v7 | "r ≥ 1", "block supported on E" wording | S1–S3 of `STATEMENTS.md` |
| v7 | Final | fully formalized on main `dccb784` |

## 8. Still missing (why)

- **K11** (4-cycle dimensions) and **Q4** (two-band saturation): explicit but long computations. FORMALIZABLE NOW.
- **S5** (spectrum ∓2α sin(2πk/N)): needs a DFT diagonalization of the circulant ⊗ J. FORMALIZABLE NOW but heavy.
- **S10** for general n (det(S+K) ≥ det S): FORMALIZABLE NOW, heavy.
- **P3–P5** (Filament theorems) and **P6–P8** (continuum, Schur and gluing bounds): FORMALIZABLE NOW, long.
- **NEEDS MISSING MATHLIB**:
  - K12 (Courant–Fischer / λ₂)
  - Q5 (principal angles)
  - Q6 (Riesz/Dunford contour calculus, Kato)
  - Q8 (zeta determinants)
  - P1–P2 (pseudospectra, Kreiss)
  - P9 (degree theory, Hausdorff dimension)
- **INTERPRETIVE**: §5. Kept as text only.

## 9. Verification (findings-v2)

`python3 scripts/check_all.py` passes. It reports 127 declarations audited (108 theorems,
18 defs, 1 structure) and 10/10 false controls rejected. Details:

* **Build:** `lake build` with no warnings.
* **Kernel replay:** `leanchecker` on all 11 modules. The root file `NonNormality.lean` only
  imports the modules and has no declarations. Replaying the root alone was OOM-killed on this
  box (more than 14 GB), so the script now skips it when it has no declarations.
* **Axioms:** only `propext`, `Classical.choice`, `Quot.sound`.
* **Lint:** Mathlib standard linter set, `#lint` and `lake exe lint-style` are all clean.
* **Headers:** Apache header on every Lean file.

See `verification/report.json`.
