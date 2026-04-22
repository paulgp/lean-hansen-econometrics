# Chapter 7 LaTeX / Lean Crosswalk

This file is a Chapter 7-only crosswalk between textbook-style mathematical statements and the Lean
theorems currently formalized in this repo.

Conventions:
- All links in this file are relative.
- The left column gives a compact LaTeX rendering of the formalized statement.
- The right column gives the corresponding Lean conclusion, not the full proof script.
- Chapter 7 public theorems live in
  [Chapter7Asymptotics.lean](../../HansenEconometrics/Chapter7Asymptotics.lean).
- Reusable convergence-in-measure helpers (WLLN, CMT, matrix inverse CMT, mulVec CMT) live in
  [AsymptoticUtils.lean](../../HansenEconometrics/AsymptoticUtils.lean).
- Chapter 7 builds on Chapter 3 least-squares algebra
  ([Chapter3LeastSquaresAlgebra.lean](../../HansenEconometrics/Chapter3LeastSquaresAlgebra.lean))
  and Chapter 4 least-squares regression
  ([Chapter4LeastSquaresRegression.lean](../../HansenEconometrics/Chapter4LeastSquaresRegression.lean)).

## Textbook-numbered results

### A7.1 Assumption 7.1 (iid + second moments + positive-definite Q)

Links:
- [Hansen excerpt](./ch7_excerpt.txt#L16)
- [Lean structure](../../HansenEconometrics/Chapter7Asymptotics.lean)

| LaTeX | Lean conclusion |
| --- | --- |
| $(Y_i, X_i)$ i.i.d., $\mathbb{E}[Y^2]<\infty$, $\mathbb{E}\lVert X\rVert^2<\infty$, $Q_{XX}=\mathbb{E}[XX']\succ 0$ | <code>SampleAssumption71 μ X e</code> |

Notes:
- The Lean structure decomposes Hansen's i.i.d. + finite-moment hypothesis into two parallel
  pairwise-independent/identically-distributed/integrable bundles, one for the outer products
  `X i (X i)ᵀ` and one for the cross products `e i • X i`. The second bundle carries the
  population orthogonality `𝔼[e X] = 0` (implied by Hansen's maintained linear-projection
  setting, lifted here into an explicit structure field).
- `Q_nonsing` uses `IsUnit (μ[X Xᵀ]).det` (equivalent to positive-definite over `ℝ` for the
  purposes of invertibility).

### T7.1 Consistency of Least Squares — sample Gram

Links:
- [Hansen excerpt](./ch7_excerpt.txt#L130)
- [Lean theorem](../../HansenEconometrics/Chapter7Asymptotics.lean)

| LaTeX | Lean conclusion |
| --- | --- |
| $\hat Q_{XX} \xrightarrow{p} Q_{XX}$ | <code>TendstoInMeasure μ (fun n ω => sampleGram (stackRegressors X n ω)) atTop (fun _ => popGram μ X)</code> |

Notes:
- Proof applies `tendstoInMeasure_wlln` to the outer-product sequence `Xᵢ Xᵢᵀ`, after rewriting
  `sampleGram (stackRegressors X n ω)` as `n⁻¹ ∑_{i<n} Xᵢ Xᵢᵀ` via Task 4
  (`sampleGram_stackRegressors_eq_avg`) and the Fin↔range bridge
  (`sum_fin_eq_sum_range_vecMulVec`).

### T7.1 Consistency — sample cross moment

Links:
- [Hansen excerpt](./ch7_excerpt.txt#L130)
- [Lean theorem](../../HansenEconometrics/Chapter7Asymptotics.lean)

| LaTeX | Lean conclusion |
| --- | --- |
| $\hat Q_{Xe} \xrightarrow{p} 0$ | <code>TendstoInMeasure μ (fun n ω => sampleCrossMoment (stackRegressors X n ω) (stackErrors e n ω)) atTop (fun _ => 0)</code> |

Notes:
- Proof applies `tendstoInMeasure_wlln` to the cross-product sequence `eᵢ • Xᵢ` and identifies
  the limit with `0` via `h.orthogonality`.

### T7.1 Consistency — inverted sample Gram

Links:
- [Hansen excerpt](./ch7_excerpt.txt#L130)
- [Lean theorem — inverse CMT](../../HansenEconometrics/AsymptoticUtils.lean)
- [Lean call site](../../HansenEconometrics/Chapter7Asymptotics.lean)

| LaTeX | Lean conclusion |
| --- | --- |
| $\hat Q_{XX}^{-1} \xrightarrow{p} Q_{XX}^{-1}$ | <code>TendstoInMeasure μ (fun n ω => (sampleGram (stackRegressors X n ω))⁻¹) atTop (fun _ => (popGram μ X)⁻¹)</code> |

Notes:
- `tendstoInMeasure_matrix_inv` provides the CMT: convergence in measure is preserved under
  `(·)⁻¹` at a pointwise-nonsingular limit. Chapter 7 instantiates it with the constant limit
  `popGram μ X` and nonsingularity hypothesis `h.Q_nonsing`.

### T7.1 Consistency — OLS estimator (core step)

Links:
- [Hansen excerpt](./ch7_excerpt.txt#L130)
- [Lean theorem](../../HansenEconometrics/Chapter7Asymptotics.lean)

| LaTeX | Lean conclusion |
| --- | --- |
| $\hat Q_{XX}^{-1} \hat Q_{Xe} \xrightarrow{p} 0$ | <code>TendstoInMeasure μ (fun n ω => (sampleGram (stackRegressors X n ω))⁻¹ *ᵥ sampleCrossMoment (stackRegressors X n ω) (stackErrors e n ω)) atTop (fun _ => 0)</code> |

Notes:
- This is the deterministic RHS of the Phase 1 OLS-error identity
  `β̂ₙ − β = Q̂ₙ⁻¹ *ᵥ ĝₙ(e)` (valid on the event `{Q̂ₙ invertible}`). Its convergence in
  probability is the mathematical content of Theorem 7.1.
- The remaining step — lifting this to `β̂ₙ → β` as stated in Hansen — requires a probabilistic
  invertibility argument: by CMT on `det`, `(Q̂ₙ).det → Q.det ≠ 0`, so the event
  `{ω : Q̂ₙ(ω) singular}` has measure → 0; on its complement the Phase 1 identity applies; off
  it, the measure shrinks. That step is mechanical and is left as a follow-up.

## Lean-only bridge results

These theorems are not direct textbook labels, but they are the key translation lemmas between
Hansen's notation and the Lean formalization.

- [`olsBetaStar`](../../HansenEconometrics/Chapter3LeastSquaresAlgebra.lean#L27):
  total OLS coefficient via `Matrix.nonsingInv`, defined on every design matrix (agreeing with
  `olsBeta` when `Xᵀ X` is invertible, returning `0` otherwise). Required for the Chapter 7
  stochastic story, where invertibility of `Xᵀ X` holds only a.s., not by typeclass.
- [`stackRegressors` / `stackErrors` / `stackOutcomes`](../../HansenEconometrics/Chapter7Asymptotics.lean):
  bridge from a pointwise `ℕ`-indexed regressor sequence to a `Fin n`-row design matrix at a
  fixed sample point `ω`.
- [`stack_linear_model`](../../HansenEconometrics/Chapter7Asymptotics.lean):
  if `yᵢ = Xᵢ · β + eᵢ` for each `i`, then
  `stackOutcomes y n ω = stackRegressors X n ω *ᵥ β + stackErrors e n ω`.
- [`sampleGram_stackRegressors_eq_avg`](../../HansenEconometrics/Chapter7Asymptotics.lean):
  `sampleGram (stackRegressors X n ω) = n⁻¹ ∑_{i<n} Xᵢ Xᵢᵀ`.
- [`sampleCrossMoment_stackRegressors_stackErrors_eq_avg`](../../HansenEconometrics/Chapter7Asymptotics.lean):
  `sampleCrossMoment (stackRegressors X n ω) (stackErrors e n ω) = n⁻¹ ∑_{i<n} eᵢ • Xᵢ`.
- [`sum_fin_eq_sum_range_vecMulVec` / `sum_fin_eq_sum_range_smul`](../../HansenEconometrics/Chapter7Asymptotics.lean):
  bridge `Fin n` summation to `Finset.range n` summation — matches Mathlib's WLLN indexing.
- [`tendstoInMeasure_wlln`](../../HansenEconometrics/AsymptoticUtils.lean):
  pairwise-independent-i.d.-integrable Banach-valued WLLN, wrapping Mathlib's `strong_law_ae`.
- [`tendstoInMeasure_continuous_comp`](../../HansenEconometrics/AsymptoticUtils.lean):
  continuous-mapping theorem for `TendstoInMeasure` along `atTop`.
- [`tendstoInMeasure_pi`](../../HansenEconometrics/AsymptoticUtils.lean):
  coordinatewise convergence in measure for Pi types over a `Fintype`.
- [`tendstoInMeasure_matrix_inv`](../../HansenEconometrics/AsymptoticUtils.lean):
  continuous-mapping theorem for matrix inversion at a pointwise-nonsingular limit.
- [`aestronglyMeasurable_matrix_inv`](../../HansenEconometrics/AsymptoticUtils.lean):
  strongly measurable functions stay strongly measurable under matrix inversion.
- [`tendstoInMeasure_prodMk`](../../HansenEconometrics/AsymptoticUtils.lean):
  joint convergence in measure on a product from coordinate-wise convergence.
- [`tendstoInMeasure_mulVec`](../../HansenEconometrics/AsymptoticUtils.lean):
  matrix-vector multiplication preserves convergence in measure.

## Pending

- Textbook-form `β̂ₙ →ₚ β`: combine
  [`sampleGramInv_mulVec_sampleCrossMoment_e_tendstoInMeasure_zero`](../../HansenEconometrics/Chapter7Asymptotics.lean)
  with the Phase 1 identity on the a.s.-invertibility event. Requires a det-CMT + triangle
  argument on the complement of `{Q̂ₙ invertible}`.
- Theorem 7.2 and onward (asymptotic normality): out of scope for Phase 2/3.
