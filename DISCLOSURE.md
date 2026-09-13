# Authorship and automation

JD Jones directed the work and is its human author and responsible
maintainer. He is not a party to the mathematics.

The recurrences and Dirichlet weights are Mazur's (*A Proof of the
Strong Papadimitriou–Ratajczak Conjecture*, public version 2026-09-09,
§§2–3), hosted at
[ProofAtlas](https://proofatlas.ai/formalizations/strong-papadimitriou-ratajczak-conjecture/)
and announced by the author on
[X, 2026-09-12](https://x.com/LechMazur/status/2098915169799733339).
The span bound, the \(n-1\) row-sum tightening, and the explicit
exponential for \(Q\) are not stated in that paper. The Lean does not
import Mazur's existence development.

## What the AI did

xAI's Grok 4.6, run through Grok Build, selected the quantitative
question from Mazur's construction, re-derived the span and weight
bounds, wrote the Python censuses, wrote the Lean 4 proofs, and wrote
this documentation. No independent human mathematical review is
recorded.

Prompt, token and monetary accounting was not retained.

## Limits

Registration at a formalization registry certifies statement matching
and kernel replay at one commit. It does not certify novelty or
significance.
