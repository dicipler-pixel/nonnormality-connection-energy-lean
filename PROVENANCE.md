# PROVENANCE

* Mathematics: Jeromie Beasley, *Non-normality is connection energy*, 17 Sept 2026, Zenodo
  record 22804072, v7 (one page). The paper cites Horn–Johnson (Matrix Analysis), Singer–Wu
  (vector diffusion maps / connection Laplacian), Kobayashi–Nomizu.
* Lean code: written from scratch for this repository on 18 Oct 2026, from the paper's
  statements. No code was copied from any other project. It uses only Mathlib (Lean v4.34.1,
  Mathlib d13f23b) and follows the conventions of `Mathlib/Combinatorics/SimpleGraph/LapMatrix.lean`
  (ordered-pair sum divided by two) and `Mathlib/Analysis/Matrix/Normed.lean` (scoped Frobenius
  norm).
* The repository set-up (toolchain, manifest, license files, the style of the check script) was
  reused from Jeromie Beasley's own `ramanujan-challenge-lean` repository.
* There was no earlier formalization of this paper. `NS_Nonnormal_Resolvent_Audit.lean`
  (10 Sept) is unrelated (Navier–Stokes) and was not used.
