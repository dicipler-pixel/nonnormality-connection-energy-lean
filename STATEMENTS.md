# STATEMENTS — "Non-normality is connection energy" (J. Beasley, 17 Sept 2026, v7)

Source: `nonnormality_is_connection_energy_v7.pdf` (one page; md5 `d7c272b3f7a04fb05f66fd3ecd353ee5`,
Zenodo record 22804072, latest version v7). Read in full with `pdftotext` and checked against the
page image.

Classes: **(a)** precise finite-dimensional linear algebra, formalizable now;
**(b)** needs analysis not in Mathlib; **(c)** heuristic, interpretive or historical, not a
mathematical statement.

Numerical checks: `numerics/check_paper.py` (output in `numerics/check_paper_output.txt`).

## Setting (definitions)

| # | Paper | Plain math | Class | Lean |
|---|---|---|---|---|
| S1 | `G = (V,E)` finite graph, `r ≥ 1` | finite simple graph on `ι`, fibre `ℂ^r` (`m` any finite type) | (a) | `G : SimpleGraph ι`, `[Fintype ι]`, `m` |
| S2 | `D = diag(D_i)`, `D_i = D_i* ∈ ℂ^{r×r}` | block diagonal with Hermitian blocks | (a) | `diagonal D : Matrix ι ι (Matrix m m ℂ)`, `hD : ∀ i, (D i).IsHermitian` |
| S3 | `A* = −A`, block supported on `E`, `A_ii = 0`, `A_ij` unitary for `{i,j} ∈ E`, so `A_ji = −A_ij*` | skew-Hermitian, zero off edges, unitary edge blocks | (a) | `IsUnitaryConnection G A`; `A_ii = 0` follows from irreflexivity; `A_ji = −A_ij*` is `IsUnitaryConnection.apply_eq_neg_conjTranspose` |
| S4 | `H = D + A` | block transport operator | (a) | `diagonal D + A`; flattened `Matrix.comp ι ι m m ℂ (diagonal D + A)` (Flatten.lean) |
| S5 | `U_ij(X) = A_ij X A_ij*`, `U_ji = U_ij⁻¹` | induced transport on `End(ℂ^r)` | (a) | used through `IsParallel`; inverse property is the unitarity of `A_ij` together with `A_ji = −A_ij*` |
| S6 | `E_A(D) := ⅛ ‖[H,H*]‖_F²` | self-commutator energy | (a) | `connectionEnergy G A D` (edge form) + identity (1) |
| S7 | `W_C` = product of `A_e` along loop `C` (up to sign), `U_C = Ad W_C` | holonomy of walks | (a) | `holonomy A p` for `p : G.Walk u v`; sign: `IsUnitaryConnection.holonomy_reverse` |
| S8 | `Fix_{Herm(r)}(Hol(i₀)) = {X ∈ Herm(r) : W_C X W_C* = X ∀ C}` | holonomy-fixed Hermitian matrices | (a) | `holonomyFixed G A i₀` (an `ℝ`-submodule) |

## Claims

| # | Paper | Plain math | Class | Status | Lean |
|---|---|---|---|---|---|
| C1 | `H* = D − A` | | (a) | proved (inside) | `selfCommutator_diagonal_add` |
| C2 | `[H,H*] = −2[D,A]` | for any star ring | (a) | **proved** | `selfCommutator_diagonal_add` |
| C3 | `[D,A]_ij = D_iA_ij − A_ijD_j = (D_i − A_ijD_jA_ij*)A_ij` | | (a) | **proved** | `diagonal_mul_sub_mul_diagonal_apply`, `norm_mul_sub_mul_eq_of_mem_unitaryGroup` |
| C4 | unitary invariance of `‖·‖_F` | | (a) | **proved** (not in Mathlib) | `frobenius_norm_unitary_mul`, `frobenius_norm_mul_unitary` |
| C5 | **(1)** `⅛‖[H,H*]‖_F² = Σ_{{i,j}∈E} ‖D_i − A_ijD_jA_ij*‖_F²` | | (a) | **proved** (ordered-pair form, edge form, flattened form) | `norm_sq_selfCommutator_div_eight`, `norm_sq_selfCommutator_div_eight_eq_sum_edgeFinset`, `norm_sq_selfCommutator_comp_div_eight` |
| C5' | summand independent of edge orientation ("two orientations") | | (a) | **proved** | `IsUnitaryConnection.norm_sub_conj_comm`, `norm_mul_sub_mul_comm` |
| C6 | **(2)** `H` normal ⇔ `D_i = A_ijD_jA_ij*` on every edge | | (a) | **proved** | `isStarNormal_iff_isParallel`, `isStarNormal_comp_iff_isParallel` |
| C7 | "i.e. exactly when `D` is parallel for the induced connection" | definitional | (a)/(c) | definition | `IsParallel` |
| C8 | (connected `G`) (2) transports `D_{i₀}` along every path; path independence ⇔ `[D_{i₀}, W_C] = 0` for all loops | | (a) | **proved** | `IsParallel.eq_conj_holonomy`, `IsUnitaryConnection.conj_holonomy_eq`, `mem_holonomyFixed_iff_commute` |
| C9 | **(3)** `ker E_A ≅ Fix_{Herm(r)} Hol_{Ad A}(i₀)` | real-linear iso by evaluation at `i₀` | (a) | **proved** (as an `ℝ`-linear equivalence) | `parallelSectionsEquivHolonomyFixed`, `mem_parallelSections_iff_connectionEnergy_eq_zero` |
| C10 | scalar specialization is the weighted Dirichlet identity | | (a) | **proved in the general (non-unitary) form** — see remark R2 | `norm_sq_selfCommutator_scalar` |
| C11 | "U is a connection on End(E) in the ordinary sense"; "classical correspondence between parallel sections and holonomy-fixed endomorphisms"; "energy measures the failure of its Hermitian obstruction field to be parallel" | interpretation in differential-geometric language | (c) | not formalized as such; its discrete content is C8–C9 | — |
| C12 | "the underlying identity and framework are classical; the present observation is the identification ..." | priority/novelty statement | (c) | not formalizable | — |
| C13 | origin in the June 18, 2026 construction `H_N = D + A`, edge term `JB_{n+1} − B_nJ` | historical | (c) | not formalizable from the paper (the objects `J`, `B_n` are not defined there) | — |

There are no class-(b) statements: everything in the paper is finite-dimensional.

## Errors and imprecisions found

No mathematical error. Identities (1), (2) and (3) are correct as stated under the stated
hypotheses (verified numerically on 300 random graphs, relative error ≤ 6e-16, and now proved in
Lean). Points worth tightening:

* **R1. Every hypothesis is used, and Hermitian `D_i` is essential.** Counterexample when it is
  dropped (one edge, `r = 1`, `A_01 = 1`, `A_10 = −1`, `D_0 = i`, `D_1 = −i`):
  `H = [[i, 1], [−1, −i]]` satisfies `HH* = H*H = 2I` (normal, `‖[H,H*]‖ = 0`), yet
  `‖D_0 − A_01 D_1 A_01*‖² = |2i|² = 4`. So (1) and (2) fail without `D_i = D_i*`.
  Proved in `checks/Necessity.lean`. Unitarity is needed for the *form* of (1): with
  `A_ij = 2U` the paper's right-hand side (read with `A⁻¹`) gives 103.3 vs. the true 413.2
  (numerics); the general correct form is `‖[H,H*]‖² = 4 Σ_{i,j} ‖D_iA_ij − A_ijD_j‖²`
  (`norm_sq_selfCommutator_eq`, no unitarity needed).
* **R2. "Weighted" Dirichlet.** Under the paper's own hypotheses the scalar edge entries are unit
  complex numbers, so the scalar case gives the *unweighted* form `Σ_{edges} (d_i − d_j)²`. The
  weighted form `4 Σ |a_ij|² (d_i − d_j)²` needs the non-unitary generalization (proved:
  `norm_sq_selfCommutator_scalar`). Suggest: "the scalar specialization (dropping unitarity)
  reduces to the weighted Dirichlet identity".
* **R3. Notation clash.** `E` is both the edge set and the bundle in `End(E)`.
* **R4. "ker E_A".** `E_A` is a quadratic function of `D`; "kernel" means its zero set inside the
  real vector space of Hermitian block-diagonal `D`. It is a subspace because `E_A` is a sum of
  squared norms of linear maps of `D`. The isomorphism in (3) is real-linear, given by `D ↦ D_{i₀}`,
  and needs `G` connected (stated in the paper).
* **R5. Orientation conventions** for `W_C` (product order, central sign `±1`) are left implicit;
  the Lean file fixes them (`holonomy`, `holonomy_reverse`: reversing a walk of length `n` gives
  `(−1)^n W*`) and shows the sign is invisible to `Ad`.

## Opposite results (found 20 October 2026, not in the v7 paper)

Found in conversation with Jeromie Beasley on 20 October 2026; checked numerically to `1e-13`
(`numerics/anti_connection_energy.py`, `anti_connection_kernel.py`, `two_books_map.py`,
`two_books_gravity.py`, outputs beside them), then proved in `NonNormality/Opposite.lean`.
Notation: `H = D + A` as above, `U_ij(X) = A_ij X A_ij*`,
`E₋ = ⅛‖[H,H*]‖² = Σ_E ‖D_i − U_ij(D_j)‖²` (identity (1)), `E₊ = ⅛‖H² − H*²‖²`.

| # | Statement | Class | Status | Lean |
|---|---|---|---|---|
| O1 | `H² − H*² = 2{D,A}` and `{D,A}_ij = D_iA_ij + A_ijD_j = (D_i + U_ij(D_j))A_ij` | (a) | **proved** | `mul_self_sub_conjTranspose_mul_self_diagonal_add`, `diagonal_mul_add_mul_diagonal_apply`, `norm_mul_add_mul_eq_of_mem_unitaryGroup` |
| O2 | **opposite identity** `E₊ = Σ_{{i,j}∈E} ‖D_i + U_ij(D_j)‖²` | (a) | **proved** (general non-unitary form too) | `norm_sq_mul_self_sub_conjTranspose_mul_self_div_eight`, `norm_sq_mul_self_sub_conjTranspose_mul_self_eq` |
| O3 | `E₊ = 0` ⇔ `H² = H*²` ⇔ `D_i = −U_ij(D_j)` on every edge (anti-parallel) | (a) | **proved** | `oppositeEnergy_eq_zero_iff`, `mul_self_eq_conjTranspose_mul_self_iff_isAntiParallel` |
| O4 | **budget** `E₋ + E₊ = 2 Σ_E (‖D_i‖² + ‖D_j‖²) = 2 Σ_i deg(i) ‖D_i‖²` | (a) | **proved** | `connectionEnergy_add_oppositeEnergy`, `connectionEnergy_add_oppositeEnergy_eq_degree` |
| O4' | `E₋ + E₊ = 2‖DA‖²` (operator form) | (a) | **proved** | `norm_sq_selfCommutator_add_norm_sq_mul_self_sub_div_eight` |
| O5 | **difference** `E₋ − E₊ = 2 Re Tr((DA)²) = 4 g(DA)`, `g(X) = ½ Re Tr(X²)` | (a) | **proved**, with `Tr` the trace of the flattened `(ι×m)×(ι×m)` matrix | `norm_sq_selfCommutator_sub_norm_sq_mul_self_sub_div_eight`, `norm_sq_add_conjTranspose_eq` |
| O6 | `H` normal and `H²` Hermitian ⇒ `Σ_i deg(i)‖D_i‖² = 0`, i.e. `D_i = 0` at every non-isolated vertex | (a) | **proved** (both forms) | `eq_zero_of_isStarNormal_of_mul_self_eq`, `sum_degree_mul_norm_sq_eq_zero_of_isStarNormal_of_mul_self_eq` |
| O7 | bipartite `G` (parts `S`, complement): flipping the sign of `D` off `S` swaps `E₋` and `E₊` | (a) | **proved** | `connectionEnergy_eq_oppositeEnergy_of_bipartite`, `oppositeEnergy_eq_connectionEnergy_of_bipartite` |
| O8 | anti-parallel `D` is transported along a walk of length `n` by `(−1)ⁿ Ad(W)` | (a) | **proved** | `IsAntiParallel.eq_conj_holonomy` |
| O9 | `ker E₊ ≅ {X ∈ Herm(r) : (−1)^{len C} W_C X W_C* = X for every loop C at i₀}` (connected `G`) | (a) | **proved** (v11, see K below) | `antiParallelSectionsEquivTwistedHolonomyFixed` |
| O10 | double-cover reading: on the bipartite double cover, cover energy of `(S+T, S−T)` is `2E₋(S) + 2E₊(T)` | (a) | **proved** (v11, see B below) | `connectionEnergy_doubleCover` |
| O11 | per-edge reflection `Γ = (d_i − d_j)/(d_i + d_j)` (scalar positive field), passive fields have `E₋,e ≤ E₊,e` | (a) | **proved** (v11, see P below) | `scalar_edge_reflection`, `norm_sub_conj_sq_le_norm_add_conj_sq_of_posSemidef` |
| O12 | "light" and "gravity" readings of the two energies (`g` as the neutral-signature trace form) | (c) | interpretation, not formalized | — |

## v11: the two books

Statements of version 11 of the paper (the one-page v7 grown into one paper carrying both books),
keyed by the letters used in the planning of v11. Numerical checks: `numerics/anti_connection_kernel.py`,
`two_books_map.py`, `two_books_duality.py`, `two_books_projectors.py`, `two_books_trace.py`,
`two_books_lockin.py` (outputs beside them). Lean: `NonNormality/AntiHolonomy.lean` (K),
`NonNormality/TwoBooks.lean` (C, P, R, B, M), `NonNormality/Passive.lean` (P, passive fields).
Notation as above; `U_ij(X) = A_ij X A_ij*`, `r = dim` of the fibre (`Fintype.card m`).

| # | Statement | Class | Status | Lean |
|---|---|---|---|---|
| K1 | `IsAntiParallel` Hermitian sections form an `ℝ`-subspace, the zero set of `E₊` | (a) | **proved** | `antiParallelSections`, `mem_antiParallelSections_iff_oppositeEnergy_eq_zero` |
| K2 | the twisted fixed set `{X ∈ Herm(r) : (−1)^{len C} W_C X W_C* = X ∀ closed walks C at i₀}` is an `ℝ`-subspace | (a) | **proved** | `twistedHolonomyFixed`, `mem_twistedHolonomyFixed_iff` |
| K3 | **twisted kernel (mirror of (3))**: connected `G`, evaluation at `i₀` is an `ℝ`-linear isomorphism `ker E₊ ≅ twisted fixed set` | (a) | **proved** | `antiParallelSectionsEquivTwistedHolonomyFixed`, `evalAntiParallel_injective`, `IsUnitaryConnection.evalAntiParallel_surjective`, `IsUnitaryConnection.twisted_conj_holonomy_eq` |
| K4 | an odd closed walk at `i₀` whose holonomy commutes with `X` (e.g. trivial holonomy) forces `X = 0` in the twisted fixed set; an anti-parallel field then vanishes at `i₀`, and on a connected graph everywhere | (a) | **proved** | `IsUnitaryConnection.eq_zero_of_mem_twistedHolonomyFixed_of_odd`, `IsAntiParallel.eq_zero_of_odd_loop`, `IsAntiParallel.eq_zero_of_odd_loop_of_connected` |
| K5 | bipartite `G` (every edge joins `S` to its complement): `D'` (= `D` on `S`, `−D` off `S`) is parallel iff `D` is anti-parallel; the sign flip is an `ℝ`-linear isomorphism `ker E₊ ≅ ker E₋` | (a) | **proved** | `isParallel_iff_isAntiParallel_of_bipartite`, `signFlip`, `antiParallelSectionsEquivParallelSections` |
| C1 | `[H + cI, (H + cI)*] = [H, H*]` for real `c` (any square matrix `H` over a star algebra with real scalars) | (a) | **proved** | `selfCommutator_add_smul_one` |
| C2 | `(H + cI)² − ((H + cI)*)² = (H² − H*²) + 2c(H − H*)`; for `H = D + A`: `= (H² − H*²) + 4cA` | (a) | **proved** | `mul_self_sub_conjTranspose_mul_self_add_smul_one`, `mul_self_sub_conjTranspose_mul_self_diagonal_add_smul_one` |
| C3 | `‖cI + T‖² = r c² + ‖T‖²` for `Tr T = 0` (no cross term) | (a) | **proved** | `norm_sq_smul_one_add_of_trace_eq_zero` |
| C4 | **trace split**, one edge: `D_i = c_i I + T_i`, `Tr T_i = 0`: `‖D_i ∓ U D_j‖² = r (c_i ∓ c_j)² + ‖T_i ∓ U T_j‖²` | (a) | **proved** | `norm_sub_conj_trace_split`, `norm_add_conj_trace_split` |
| C5 | **trace split**, summed: `E∓(D) = r Σ_E (c_i ∓ c_j)² + E∓(T)` | (a) | **proved** (ordered-pair form of the scalar edge sum, divided by 2) | `connectionEnergy_trace_split`, `oppositeEnergy_trace_split` |
| P1 | real Frobenius inner product `⟨a,b⟩ = Re Tr(a* b)`; `= Re Tr(a b)` for Hermitian `a`; symmetric; `‖a ± b‖² = ‖a‖² + ‖b‖² ± 2⟨a,b⟩` | (a) | **proved** | `frobeniusInner`, `frobeniusInner_eq_re_trace_mul`, `frobeniusInner_comm`, `norm_sq_add_eq`, `norm_sq_sub_eq` |
| P2 | Cauchy–Schwarz `⟨a,b⟩² ≤ ‖a‖² ‖b‖²` (so `L² ≥ 0`) | (a) | **proved** (discriminant of `t ↦ ‖t a − b‖²`) | `frobeniusInner_sq_le` |
| P3 | **per-edge duality** `P² + V² + L² = 1`, `s = ‖a‖² + ‖b‖² ≠ 0`, `P = (‖a‖² − ‖b‖²)/s`, `V = (‖a+b‖² − ‖a−b‖²)/(‖a+b‖² + ‖a−b‖²)`, `L² = 4(‖a‖²‖b‖² − ⟨a,b⟩²)/s²` | (a) | **proved** (for any `a, b`, Hermitian or not, with `⟨a,b⟩ = Re Tr(a* b)`) | `duality_sum_sq` |
| P4 | `P² + V² ≤ 1` | (a) | **proved** | `duality_le_one` |
| P5 | scalar edge: `(d_i − d_j)² = Γ² (d_i + d_j)²`, `Γ = (d_i − d_j)/(d_i + d_j)`, `d_i + d_j ≠ 0`; `(d_i + d_j)² − (d_i − d_j)² = 4 d_i d_j` | (a) | **proved** | `scalar_edge_reflection`, `scalar_edge_flux` |
| P6 | **passive fields**: `a, b ⪰ 0` ⇒ `Re Tr(a b) ≥ 0` ⇒ `‖a − b‖² ≤ ‖a + b‖²`; on an edge with PSD blocks `E₋,e ≤ E₊,e` (`|Γ_e| ≤ 1`) | (a) | **proved** (via the positive square root `CFC.sqrt`) | `re_trace_mul_nonneg_of_posSemidef`, `norm_sub_sq_le_norm_add_sq_of_posSemidef`, `norm_sub_conj_sq_le_norm_add_conj_sq_of_posSemidef` |
| P7 | `Γ = tanh(ln(d_i/d_j)/2)` | (a) | not formalized (elementary; not needed by the Lean development) | — |
| R1 | Hermitian idempotent `P` with `Tr P = k` has `‖P‖² = k` | (a) | **proved** | `norm_sq_of_projector` |
| R2 | **projector fields**: `‖P − R‖² + ‖P + R‖² = 4k` (so `E₊,e = 4k − E₋,e`); with transport `R = U P_j U*` | (a) | **proved** | `norm_sub_sq_add_norm_add_sq_of_projector`, `norm_sub_conj_sq_add_norm_add_conj_sq_of_projector` |
| R3 | projector fields, summed: `E₋ + E₊ = 4k |E|` | (a) | **proved** | `connectionEnergy_add_oppositeEnergy_of_projector` |
| R4 | `E₋,e = 2 Σ sin²θ_a`, `E₊,e = 2 Σ (1 + cos²θ_a)` in principal angles | (a) | not formalized (principal angles are not in the Lean development; R2 is the content used) | — |
| B1 | the bipartite double cover `G̃` on `ι × Bool` and the lifted connection `Ã` (same transport on both lifted edges); `Ã` is a unitary connection on `G̃` | (a) | **proved** | `doubleCover`, `liftConnection`, `IsUnitaryConnection.liftConnection`, `doubleCover_adj_imp` |
| B2 | one edge: `‖(S_i+T_i) − U(S_j−T_j)‖² + ‖(S_i−T_i) − U(S_j+T_j)‖² = 2‖S_i − U S_j‖² + 2‖T_i + U T_j‖²` | (a) | **proved** | `doubleCover_edge_core` |
| B3 | **double cover**: `E₋^{G̃}(S+T, S−T) = 2E₋(S) + 2E₊(T)` | (a) | **proved** (the cover graph is modelled, not only the per-edge core; holds for any block matrix `A`, unitarity is not needed) | `connectionEnergy_doubleCover`, `coverField`, `coverField_isHermitian` |
| M1 | `E₋ E₊ = ((E₋+E₊)/2)² − ((E₋−E₊)/2)²` | (a) | **proved** (trivial identity) | `mul_eq_half_add_sq_sub_half_sub_sq` |
| M2 | with `E₋ + E₊ = 2‖DA‖²`, `E₋ − E₊ = 2 Re Tr((DA)²)`: `E₋ E₊ = ‖DA‖⁴ − (Re Tr((DA)²))²` | (a) | **proved** (`Tr` of the flattened `(ι×m)×(ι×m)` matrix, as in O5) | `connectionEnergy_mul_oppositeEnergy` |
| O | ring floors (`two_books_lockin.py`): `Σ_k (1 − cos x_k) ≥ min_w N(1 − cos((d − 2πw)/N))` under `Σ x_k ≡ d (mod 2π)` | (b)/(a) | **not proved** (a constrained minimisation; left out of the Lean development, numerically checked only) | — |

False controls added in v11 (each with a proved negation in `checks/Negations.lean`):
`constant_shift_two_cA_wrong` (`2cA` for `4cA`), `duality_without_third_leg_wrong` (`P² + V² = 1`),
`projector_budget_two_k_wrong` (`2k` for `4k`), `double_cover_missing_factor_two_wrong`
(`E₋(S) + E₊(T)` for `2E₋(S) + 2E₊(T)`).
