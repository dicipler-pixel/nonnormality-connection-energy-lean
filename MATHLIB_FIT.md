# MATHLIB_FIT — what could go to Mathlib, and an honest verdict

Surveyed against the pinned Mathlib `d13f23b` (24 Sept 2026, tag `v4.34.1`) by searching the
source tree on this box. Open Mathlib PRs were **not** checked (that needs GitHub; re-check before
posting anything).

## 1. What Mathlib already has (exact names)

| Concept | Mathlib name |
|---|---|
| normal element | `IsStarNormal` (class, `Mathlib/Algebra/Star/SelfAdjoint.lean`), `isStarNormal_iff : IsStarNormal x ↔ Commute (star x) x` |
| Hermitian matrix | `Matrix.IsHermitian`, `Matrix.IsHermitian.add`, `Matrix.IsHermitian.smul`, `Matrix.isHermitian_zero` |
| unitary matrices | `Matrix.unitaryGroup`, `Matrix.mem_unitaryGroup_iff`, `Matrix.mem_unitaryGroup_iff'` |
| Frobenius norm | scoped instances `Matrix.Norms.Frobenius` (`Matrix.frobeniusNormedAddCommGroup`, …), `Matrix.frobenius_norm_def` (rpow form), `Matrix.frobenius_norm_conjTranspose`, `Matrix.frobenius_norm_transpose`, `Matrix.frobenius_norm_mul` (submultiplicativity), `Matrix.frobenius_norm_map_eq` |
| block matrices | `Matrix.comp`, `Matrix.compRingEquiv`, `Matrix.compAlgEquiv` (`Mathlib/Data/Matrix/Composition.lean`; transpose lemmas only) |
| graph Laplacian | `SimpleGraph.lapMatrix`, `SimpleGraph.lapMatrix_toLinearMap₂'` (`xᵀLx = (∑ᵢⱼ [i~j](xᵢ−xⱼ)²)/2`), `lapMatrix_toLinearMap₂'_apply'_eq_zero_iff_forall_reachable`, `SimpleGraph.lapMatrix_ker_basis` (kernel ≅ functions on connected components) |
| walks | `SimpleGraph.Walk`, `Walk.reverse_cons`, `Walk.cons_append`, `Walk.concat_eq_append`, `SimpleGraph.Connected.preconnected` |
| spectral theorem | `Matrix.IsHermitian.spectral_theorem` |

**Not in Mathlib** (searched, no hits): matrix commutator / self-commutator API, unitary invariance
of the Frobenius norm, `‖A‖² = re tr(AᴴA)`, a `‖A‖²`-as-sum lemma without `rpow`, Schur
triangulation, Henrici's departure from normality, graph connections / connection Laplacian /
holonomy, `conjTranspose` lemmas for `Matrix.comp`, and a lemma turning a sum over ordered adjacent
pairs into a sum over `edgeFinset`.

## 2. Genuinely new lemmas, suggested names and homes

Small, general, low-risk — these are the realistic first PRs:

| Lemma here | Suggested Mathlib name | Home |
|---|---|---|
| `frobenius_norm_sq` | `Matrix.frobenius_norm_sq` (`‖A‖ ^ 2 = ∑ i, ∑ j, ‖A i j‖ ^ 2`) | `Mathlib/Analysis/Matrix/Normed.lean` |
| `frobenius_norm_sq_eq_re_trace` | `Matrix.frobenius_norm_sq_eq_re_trace` | same file (needs `Trace` import) or `Mathlib/Analysis/CStarAlgebra/Matrix.lean` |
| `frobenius_norm_unitary_mul`, `frobenius_norm_mul_unitary` | `Matrix.frobenius_norm_unitary_mul`, `Matrix.frobenius_norm_mul_unitary` | `Mathlib/Analysis/CStarAlgebra/Matrix.lean` (next to `entry_norm_bound_of_unitary`) |
| `comp_conjTranspose` | `Matrix.comp_conjTranspose` (square blocks) | `Mathlib/Data/Matrix/Composition.lean` (beside `comp_transpose`); could upgrade `compAlgEquiv` to a `StarAlgEquiv` |
| `frobenius_norm_comp` | `Matrix.frobenius_norm_comp` | `Mathlib/Analysis/Matrix/Normed.lean` |
| `sum_sum_ite_adj_eq_two_mul_sum_edgeFinset` | `SimpleGraph.sum_ite_adj_eq_two_nsmul_sum_edgeFinset` | `Mathlib/Combinatorics/SimpleGraph/DegreeSum.lean` |
| `selfCommutator_diagonal_add` | (only with a commutator API) | `Mathlib/Data/Matrix/…` |

Larger and more specialized:

| Result | Assessment |
|---|---|
| identity (1) `norm_sq_selfCommutator_div_eight` | A short computation once the lemmas above exist. On its own reviewers will likely call it too specialized ("a paper result, not library material"). |
| identity (2) `isStarNormal_iff_isParallel` | Same. |
| identity (3) `parallelSectionsEquivHolonomyFixed` | The interesting one: it is the connection version of `lapMatrix_ker_basis` / `…_eq_zero_iff_forall_reachable`. It would fit Mathlib only inside a general **connection Laplacian on a graph** API (Singer–Wu), which Mathlib does not have. |

## 3. Overlaps and risks

* No overlap with existing Mathlib declarations (no name clashes; checked by building against the
  pinned Mathlib).
* Open PRs not checked: someone may already be adding unitary invariance of the Frobenius norm or
  a commutator API. Search Zulip and the PR queue first.
* `Matrix ι ι (Matrix m m ℂ)` with nested Frobenius norms is an unusual setting for Mathlib; a PR of
  the headline results would probably be asked to use `Matrix (ι × m) (ι × m) ℂ` or linear maps
  on `ι → EuclideanSpace ℂ m` (the flattened versions in `Flatten.lean` are a start).

## 4. Honest verdict

* **The paper's headline identity is correct and now fully machine-checked**, but it is an
  elementary computation (the paper itself says the underlying identity is classical). Mathlib
  is unlikely to accept "Non-normality is connection energy" as a file by itself.
* **What Mathlib would realistically accept now:** the 5–6 general lemmas in §2 (Frobenius norm
  squared/trace/unitary invariance, `Matrix.comp` and `conjTranspose`, the edge-sum lemma). They
  are small, fill clear gaps, and are the honest "first contribution".
* **A bigger, worthwhile contribution:** a `SimpleGraph` connection Laplacian with unitary edge
  blocks, generalizing `lapMatrix`, with the energy identity and the kernel ≅ holonomy-fixed
  theorem (3). Identities (1)–(2) would then be corollaries. That is a real design discussion for
  Zulip first, not a cold PR.
* Compared with the Ramanujan 2.1 piece: no challenge-rule grey area, Mathlib-only, fully closed.
  But the Ramanujan piece's general Euler integral for `₂F₁` is a more obviously "wanted" Mathlib
  theorem; this one is cleaner but smaller.
