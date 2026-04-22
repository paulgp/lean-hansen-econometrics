# Chapter 14 LaTeX / Lean Crosswalk

This file is a chapter-level crosswalk between textbook statements and Lean formalizations.

Conventions:
- All links in this file are relative.
- At this stage the middle column is a compact theorem-surface summary, not necessarily a polished LaTeX rendering.
- Leave the Lean column blank unless the repo already contains a real theorem.
- Use this file for statement-level mapping; use [inventory.md](./inventory.md) for chapter status and planning.

## Links

- [Inventory](./inventory.md)
- [Hansen excerpt](./ch14_excerpt.txt)

## Crosswalk

| Textbook result | Textbook statement | Lean theorem |
| --- | --- | --- |
| Theorem 14.1 | If Yt is i.i.d., then it strictly stationary. |  |
| Theorem 14.2 | If Yt is strictly stationary and Xt = φ(Yt ,Yt −1,Yt −2,...) ∈ Rq is a |  |
| Theorem 14.3 | If Yt is strictly stationary, E |#124;Y |#124;< ∞, and ∑∞ |  |
| Theorem 14.4 | If Yt ∈ Rm is i.i.d. then it strictly stationary and ergodic. |  |
| Theorem 14.5 | If Yt ∈ Rm is strictly stationary and ergodic and Xt = |  |
| Theorem 14.6 | If Yt is strictly stationary, ergodic, E |#124;Y |#124;< ∞, and ∑∞ |  |
| Theorem 14.7 | If Yt ∈ R is strictly stationary, ergodic, and E |  |
| Theorem 14.8 | A stationary series Yt ∈ Rm is ergodic iff for all events A and B |  |
| Theorem 14.9 | Ergodic Theorem . |  |
| Theorem 14.10 | If (et , Ft ) is a MDS and E |  |
| Theorem 14.11 | MDS CLT If ut is a strictly stationary and ergodic martingale |  |
| Theorem 14.12 | If Yt has mixing coefﬁcients αY (ℓ) and Xt = |  |
| Theorem 14.13 | Let F t |  |
| Theorem 14.14 | If Yt is i.i.d. then it is strong mixing and ergodic. |  |
| Theorem 14.15 | If ut is strictly stationary with mixing coefﬁcientsα(ℓ), E[ut ] = |  |
| Theorem 14.16 | If Yt ∈ R is covariance stationary it has the projection equation |  |
| Theorem 14.17 | The Wold Decomposition If Yt is covariance stationary and |  |
| Theorem 14.18 | If Yt is covariance stationary and non-deterministic then Yt |  |
| Theorem 14.19 | If Yt is covariance stationary, non-deterministic, with Wold |  |
| Theorem 14.21 | If E |#124;et |#124;< ∞ and |#124;α1|#124;< 1 then the AR(1) process (14.25) has the |  |
| Theorem 14.22 | If E |#124;et |#124;< ∞ and |  |
| Theorem 14.23 | If E |#124;et |#124;< ∞ and all roots of α(z) lie outside the unit circle then |  |
| Theorem 14.24 | If all roots r j of the autoregressive polynomial α(z) satisfy⏐⏐r j |  |
| Theorem 14.25 | The ARMA(p,q) process (14.38) is strictly stationary and er- |  |
| Theorem 14.26 | Suppose that Yt = µ + ∑∞ |  |
| Theorem 14.27 | In the AR(p) model (14.38), if 0 < σ2 < ∞ then Q > 0 and α is |  |
| Theorem 14.28 | If Yt is strictly stationary, not purely deterministic, and |  |
| Theorem 14.29 | If Yt is strictly stationary, ergodic, not purely deterministic, |  |
| Theorem 14.30 | If Yt follows the AR(p) model (14.38), all roots of a(z) lie out- |  |
| Theorem 14.31 | Under the assumptions of Theorem 14.30, if in addition |  |
| Theorem 14.32 | Assume that Yt is strictly stationary, ergodic, and for somer > |  |
| Theorem 14.33 | Under the assumptions of Theorem 14.32, as n → ∞, ˆV − →p V |  |
| Theorem 14.34 | Under the assumptions of Theorem 14.32 plus∑∞ |  |
| Theorem 14.35 | If (Yt , Xt ) is strictly stationary, ergodic, with ﬁnite second mo- |  |
| Theorem 14.36 | For any r > 0, as n → ∞, n−1−r ∑n |  |

## Notes

- This is currently a theorem-surface map for the chapter.
- The Lean column is intentionally left blank until there is actual formalization to link.
