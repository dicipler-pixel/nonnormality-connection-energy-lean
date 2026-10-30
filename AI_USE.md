# AI use

## Dated log

* 18 October 2026 (America/Chicago): the Lean formalization, the numerical checks, the check
  script and the prose files in this repository were drafted by an AI assistant (Grok Bot) at
  Jeromie Beasley's request, from his paper. Every Lean statement is machine-checked; the prose
  was not independently reviewed.
* 20 October 2026: `NonNormality/Opposite.lean`, its false controls, the CI workflow and the
  corresponding prose updates were drafted by an AI assistant (Claude) at Jeromie Beasley's
  request. Every Lean statement is machine-checked in CI; the prose was not independently
  reviewed.
* 20 October 2026, version 11: `NonNormality/AntiHolonomy.lean`, `NonNormality/TwoBooks.lean`,
  `NonNormality/Passive.lean`, `checks/Negations.lean`, the four new false controls and the
  corresponding prose updates were drafted by an AI assistant (Claude) at Jeromie Beasley's
  request. Every Lean statement is machine-checked in CI; the prose was not independently
  reviewed.
* 21 to 28 October 2026: the later commits on `main` (the admissible-switching results, the v15
  census and `CITATION.cff`) carry `Co-Authored-By: Claude Opus 5.5` in their commit messages.
  That code and prose were drafted by Claude Opus 5.5, run by Jeromie Beasley, at his request.

## Author's disclosure

I am Jeromie N. Beasley. This line of work goes back to June 2026, to versions 1 and 2 of
*Spectral Stability Across Obstruction Interfaces in Geometric Transport Systems: Effective
Inertia Tensors and Gluing Dynamics* on Zenodo (23 and 24 June 2026). Early on I used only Grok
and GPT; I now also use Claude. I ask the AI questions of mathematics and physics, learn their
general applications, and use it where it is needed.

AI wrote the mathematics of the paper *Non-normality is connection energy* (Zenodo concept DOI
10.5281/zenodo.22803572) under my direction, and I directed all the work in this repository:
which statements to formalize, in what order, and what to check. The numerical scripts in
`numerics/` were drafted by AI at my request (see the log above).

Models used:

* **Claude Opus 5.5** (Anthropic), run by me: drafted Lean proofs, false controls, CI, numerics
  and prose (see the commit trailers and the log above).
* **Grok Bot** assistants: drafted the first formalization, numerical checks and prose
  (18 October 2026), and later checked the repository and the compiled volume.
* **SAIR Open Math AI** (Open Math OS, team Mad Hatters): compiled and checked the volume
  `nonnormality_connection_energy_complete_v1.pdf` and re-ran the Lean audits.
* **GPT** (OpenAI): part of the research behind this work from the start (June 2026 on); it did
  not work on this repository and wrote none of its files.

**Provenance of the Lean proofs (Lean Pool's categories): `AI`.** The Lean was drafted by AI at
my direction; I did not write the proofs by hand.

## What is checked and what is not

* Every Lean statement is checked by Lean's kernel. At commit
  `a98c8819c8bfd358909502cdffe79f229d0db16b` the sources contain no `sorry`, `admit` or
  `native_decide` and declare no custom axioms; `#print axioms` shows only the standard
  `propext`, `Classical.choice` and `Quot.sound`. The false controls in `FalseControls/` must
  fail to compile.
* Lean checks the statements as written. Whether they say what the paper means is a human
  judgement; see `STATEMENTS.md` and `LIMITATIONS.md`.
* The prose files were drafted by AI and have not been independently reviewed. I am the only
  reader on my end; I read all of it, to gain the understanding I asked the AI for.
* Not everything in the paper is formalized; see `LIMITATIONS.md`.

## Contact

GitHub [dicipler-pixel](https://github.com/dicipler-pixel) ·
X [@d1c1pler](https://x.com/d1c1pler) ·
YouTube [@AtlasMemoriae](https://www.youtube.com/@AtlasMemoriae) ·
[atlas-memoriae.dicipler.workers.dev](https://atlas-memoriae.dicipler.workers.dev) ·
ORCID [0009-0006-4645-5643](https://orcid.org/0009-0006-4645-5643)
