# Chapter 2 LaTeX / Lean Crosswalk

This file is a Chapter 2-only crosswalk between textbook-style mathematical statements and the Lean
theorems currently formalized in this repo.

Conventions:
- All links in this file are relative.
- The left column gives a compact LaTeX rendering of the formalized statement.
- The right column gives the corresponding Lean conclusion, not the full proof script.
- When the Lean theorem is more general than Hansen's statement, the notes call that out explicitly.
- This file avoids raw HTML `<pre>` blocks, since many Markdown math renderers do not parse LaTeX
  inside HTML or code/pre blocks.

## Textbook-numbered results

### T2.1 Simple Law of Iterated Expectations

Links:
- [Hansen excerpt](./ch2_excerpt.txt#L491)
- [Lean theorem](../../HansenEconometrics/Chapter2CondExp.lean#L18)

| LaTeX | Lean conclusion |
| --- | --- |
| $\int \mathbb{E}[Y \mid \mathcal{G}] \, d\mu = \int Y \, d\mu$ | <code>∫ ω, (μ[Y &#124; m]) ω ∂μ = ∫ ω, Y ω ∂μ</code> |

Notes:
- Lean is stated for a sub-σ-algebra `m ≤ m₀`.

### T2.2 Tower Property

Links:
- [Hansen excerpt](./ch2_excerpt.txt#L543)
- [General sigma-algebra form](../../HansenEconometrics/Chapter2CondExp.lean#L26)
- [`X₁, X₂` wrapper](../../HansenEconometrics/Chapter2CondExp.lean#L37)

| LaTeX | Lean conclusion |
| --- | --- |
| $\mathbb{E}[\mathbb{E}[Y \mid \mathcal{G}_2] \mid \mathcal{G}_1] = \mathbb{E}[Y \mid \mathcal{G}_1]$ for $\mathcal{G}_1 \subseteq \mathcal{G}_2$ | <code>μ[μ[Y &#124; m₂] &#124; m₁] =ᵐ[μ] μ[Y &#124; m₁]</code> |

Notes:
- Lean also includes the textbook-shaped `E[E[Y | X₁, X₂] | X₁] = E[Y | X₁]` wrapper.

### T2.3 Conditioning Theorem

Links:
- [Hansen excerpt](./ch2_excerpt.txt#L587)
- [Almost-everywhere pull-out form](../../HansenEconometrics/Chapter2CondExp.lean#L54)
- [Integrated form](../../HansenEconometrics/Chapter2CondExp.lean#L65)

| LaTeX | Lean conclusion |
| --- | --- |
| $\mathbb{E}[gY \mid \mathcal{G}] = g \, \mathbb{E}[Y \mid \mathcal{G}]$ | <code>μ[(fun ω => g ω * Y ω) &#124; m] =ᵐ[μ] fun ω => g ω * (μ[Y &#124; m]) ω</code> |
| $\int gY \, d\mu = \int g \, \mathbb{E}[Y \mid \mathcal{G}] \, d\mu$ | <code>∫ ω, g ω * Y ω ∂μ = ∫ ω, g ω * (μ[Y &#124; m]) ω ∂μ</code> |

### T2.4 Properties of the CEF Error

Links:
- [Hansen excerpt](./ch2_excerpt.txt#L632)
- [T2.4.1 conditional mean zero](../../HansenEconometrics/Chapter2CondExp.lean#L78)
- [T2.4.2 unconditional mean zero](../../HansenEconometrics/Chapter2CondExp.lean#L102)
- [T2.4.4 orthogonality](../../HansenEconometrics/Chapter2CondExp.lean#L114)

| LaTeX | Lean conclusion |
| --- | --- |
| $\mathbb{E}[e \mid \mathcal{G}] = 0$ | <code>μ[cefError (μ := μ) Y m &#124; m] =ᵐ[μ] 0</code> |
| $\int e \, d\mu = 0$ | <code>∫ ω, cefError (μ := μ) Y m ω ∂μ = 0</code> |
| $\int g e \, d\mu = 0$ for $g$ measurable w.r.t. $\mathcal{G}$ | <code>∫ ω, g ω * cefError (μ := μ) Y m ω ∂μ = 0</code> |

### T2.5 Finite Regression-error Variance

Links:
- [Hansen excerpt](./ch2_excerpt.txt#L691)
- [Lean theorem](../../HansenEconometrics/Chapter2Variance.lean#L28)

| LaTeX | Lean conclusion |
| --- | --- |
| $\mathbb{E}[Y^2] < \infty \Longrightarrow \mathbb{E}[e^2] < \infty$ | <code>MemLp (cefError μ Y m) 2 μ</code> |

Notes:
- Lean states this directly as square-integrability of the CEF error.

### T2.6 More Information Weakly Reduces Residual Variance

Links:
- [Hansen excerpt](./ch2_excerpt.txt#L711)
- [Lean theorem](../../HansenEconometrics/Chapter2Variance.lean#L76)

| LaTeX | Lean conclusion |
| --- | --- |
| $\operatorname{Var}(Y - \mathbb{E}[Y \mid \mathcal{G}_2]) \le \operatorname{Var}(Y - \mathbb{E}[Y \mid \mathcal{G}_1])$ for $\mathcal{G}_1 \subseteq \mathcal{G}_2$ | <code>Var[cefError μ Y m₂; μ] ≤ Var[cefError μ Y m₁; μ]</code> |

Notes:
- Lean is stated in sigma-algebra form, which is slightly more general than the textbook wording.

### T2.7 Conditional Expectation as Best Predictor

Links:
- [Hansen excerpt](./ch2_excerpt.txt#L778)
- [Sigma-algebra form](../../HansenEconometrics/Chapter2CondExp.lean#L175)
- [`E[Y | X]` wrapper](../../HansenEconometrics/Chapter2CondExp.lean#L232)

| LaTeX | Lean conclusion |
| --- | --- |
| $\mathbb{E}[(Y - g)^2] \ge \mathbb{E}[(Y - \mathbb{E}[Y \mid \mathcal{G}])^2]$ | <code>∫ ω, (Y ω - (μ[Y &#124; m]) ω)^2 ∂μ ≤ ∫ ω, (Y ω - g ω)^2 ∂μ</code> |
| $\mathbb{E}[(Y - g(X))^2] \ge \mathbb{E}[(Y - \mathbb{E}[Y \mid X])^2]$ | <code>∫ ω, (Y ω - (μ[Y &#124; mβ.comap X]) ω)^2 ∂μ ≤ ∫ ω, (Y ω - g ω)^2 ∂μ</code> |

### T2.8 Law of Total Variance

Links:
- [Hansen excerpt](./ch2_excerpt.txt#L847)
- [Main identity](../../HansenEconometrics/Chapter2Variance.lean#L35)
- [Rearranged form](../../HansenEconometrics/Chapter2Variance.lean#L45)

| LaTeX | Lean conclusion |
| --- | --- |
| $\operatorname{Var}(Y) = \mathbb{E}[\operatorname{Var}(Y \mid \mathcal{G})] + \operatorname{Var}(\mathbb{E}[Y \mid \mathcal{G}])$ | <code>μ[Var[Y; μ &#124; m]] + Var[μ[Y &#124; m]; μ] = Var[Y; μ]</code> |
| $\operatorname{Var}(Y) = \mathbb{E}[\operatorname{Var}(Y \mid \mathcal{G})] + \operatorname{Var}(\mathbb{E}[Y \mid \mathcal{G}])$ | <code>Var[Y; μ] = μ[Var[Y; μ &#124; m]] + Var[μ[Y &#124; m]; μ]</code> |

### T2.9 Linear Projection Model

Links:
- [Hansen excerpt](./ch2_excerpt.txt#L1448)
- [Normal equations](../../HansenEconometrics/Chapter2LinearProjection.lean#L25)
- [Orthogonality](../../HansenEconometrics/Chapter2LinearProjection.lean#L34)
- [Criterion at `β`](../../HansenEconometrics/Chapter2LinearProjection.lean#L52)
- [Quadratic completion](../../HansenEconometrics/Chapter2LinearProjection.lean#L62)
- [Minimization](../../HansenEconometrics/Chapter2LinearProjection.lean#L96)
- [Moment wrapper](../../HansenEconometrics/Chapter2LinearProjection.lean#L108)

| LaTeX | Lean conclusion |
| --- | --- |
| $Q_{XX} \beta = Q_{XY}$ | <code>QXX *ᵥ linearProjectionBeta QXX QXY = QXY</code> |
| $Q_{XY} - Q_{XX} \beta = 0$ | <code>QXY - QXX *ᵥ linearProjectionBeta QXX QXY = 0</code> |
| $S(\beta) = Q_{YY} - \beta' Q_{XY}$ | <code>linearProjectionMSE QXX QXY QYY (linearProjectionBeta QXX QXY) = QYY - linearProjectionBeta QXX QXY ⬝ᵥ QXY</code> |
| $S(b) = S(\beta) + (b - \beta)' Q_{XX} (b - \beta)$ | <code>linearProjectionMSE QXX QXY QYY b =</code><br><code>linearProjectionMSE QXX QXY QYY (linearProjectionBeta QXX QXY)</code><br><code>+ (b - linearProjectionBeta QXX QXY) ⬝ᵥ (QXX *ᵥ (b - linearProjectionBeta QXX QXY))</code> |
| $S(\beta) \le S(b)$ | <code>linearProjectionMSE QXX QXY QYY (linearProjectionBeta QXX QXY) ≤ linearProjectionMSE QXX QXY QYY b</code> |
| If $EXX = E[XX']$, $EXY = E[XY]$, and $EY2 = E[Y^2]$, then $S(\beta) \le S(b)$ | <code>linearProjectionMSE EXX EXY EY2 (linearProjectionBeta EXX EXY) ≤ linearProjectionMSE EXX EXY EY2 b</code> |

Notes:
- The last row is the textbook moment wrapper for the minimization statement.
- Lean also includes the uniqueness result [`linearProjectionBeta_eq_of_MSE_eq`](../../HansenEconometrics/Chapter2LinearProjection.lean#L119).

### T2.10 Regression Coefficients

Links:
- [Hansen excerpt](./ch2_excerpt.txt#L1765)
- [Intercept formula](../../HansenEconometrics/Chapter2LinearProjection.lean#L229)
- [Slope formula](../../HansenEconometrics/Chapter2LinearProjection.lean#L258)

| LaTeX | Lean conclusion |
| --- | --- |
| $\alpha = \mu_Y - \mu_X' \beta$ | <code>α = ∫ ω, Y ω ∂μ - meanVec μ X ⬝ᵥ β</code> |
| $\beta = \operatorname{var}[X]^{-1} \operatorname{cov}(X, Y)$ | <code>β = linearProjectionBeta (covMat μ X) (covVec μ X Y)</code> |

Notes:
- The slope formula is a covariance-form corollary of the earlier normal-equations theorem.

## Lean-only bridge results

These theorems are not direct textbook labels, but they are the key translation lemmas between
Hansen's notation and the Lean formalization.

- [`condExpL2_minimal`](../../HansenEconometrics/Chapter2CondExp.lean#L137):
  $\lVert Y - \mathbb{E}[Y \mid m] \rVert_2 \le \lVert Y - g \rVert_2$ in the $L^2$ projection language
  used by Mathlib.
- [`integral_condVar_eq_integral_cefError_sq`](../../HansenEconometrics/Chapter2Variance.lean#L16):
  $\int \operatorname{Var}(Y \mid \mathcal{G}) \, d\mu = \int e^2 \, d\mu$.
- [`variance_condExp_le_variance`](../../HansenEconometrics/Chapter2Variance.lean#L55):
  $\operatorname{Var}(\mathbb{E}[Y \mid \mathcal{G}]) \le \operatorname{Var}(Y)$.
- [`linearProjectionBeta_eq_of_normal_equations`](../../HansenEconometrics/Chapter2LinearProjection.lean#L41):
  solves $Q_{XX} b = Q_{XY}$ as $b = Q_{XX}^{-1} Q_{XY}$.
- [`integral_dotProduct_eq_meanVec_dotProduct`](../../HansenEconometrics/Chapter2LinearProjection.lean#L158):
  $\int X' b \, d\mu = (\int X \, d\mu)' b$.
- [`covVec_dotProduct_eq_covMat_mulVec`](../../HansenEconometrics/Chapter2LinearProjection.lean#L174):
  $\operatorname{cov}(X, X' b) = \operatorname{covMat}(X) b$.
- [`covVec_linearProjectionModel`](../../HansenEconometrics/Chapter2LinearProjection.lean#L191):
  $\operatorname{cov}(X, \alpha + X' \beta + e) = \operatorname{covMat}(X)\beta +
  \operatorname{cov}(X, e)$.
