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
* The opposite results (`NonNormality/Opposite.lean`: the anticommutator identity, the budget,
  the sum and difference of the two energies, the normal-and-Hermitian-square corollary, the
  bipartite swap) were found on 20 October 2026 in conversation with Jeromie Beasley. The
  numerical checks are his (`numerics/anti_connection_energy.py`, `anti_connection_kernel.py`,
  `two_books_map.py`, `two_books_gravity.py`, with their outputs), copied unchanged. The Lean
  proofs were written on 20 October 2026 from those statements, mirroring the proofs of
  identities (1) and (2) in `SelfCommutator.lean`; no code was copied from any other project.
* Version 11 ("the two books", 20 October 2026): `NonNormality/AntiHolonomy.lean`,
  `NonNormality/TwoBooks.lean`, `NonNormality/Passive.lean`, the four false controls
  `constant_shift_two_cA_wrong`, `duality_without_third_leg_wrong`, `projector_budget_two_k_wrong`,
  `double_cover_missing_factor_two_wrong` and their negations in `checks/Negations.lean`. The
  statements were planned with Jeromie Beasley on 20 October 2026; the numerical checks are his
  (`numerics/two_books_duality.py`, `two_books_projectors.py`, `two_books_trace.py`,
  `two_books_lockin.py`, with outputs), copied unchanged. The Lean proofs were written on
  20 October 2026 from those statements; no code was copied from any other project.
