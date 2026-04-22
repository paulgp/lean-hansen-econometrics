# Chapter 5 LaTeX / Lean Crosswalk

This file maps Chapter 5 textbook statements to the current Lean formalization.

Conventions:
- All links in this file are relative.
- The Lean column gives the linked theorem or definition name plus the core conclusion when the repo
  already contains a real result.
- Blank Lean cells mark statements that are still pending.

## Links

- [Inventory](./inventory.md)
- [Hansen excerpt](./ch5_excerpt.txt)
- [Lean file](../../HansenEconometrics/Chapter5NormalRegression.lean)

## Crosswalk

| Textbook result | LaTeX | Lean theorem |
| --- | --- | --- |
| Theorem 5.1 standard normal moments | If $Z \sim N(0,1)$, then all integer moments are finite, odd moments vanish, $\mathbb{E}[Z^{2m}] = (2m-1)!!$, and for $r > 0$, $\mathbb{E}[|Z|^r] = 2^{r/2} \pi^{-1/2} \Gamma\!\left(\frac{r+1}{2}\right)$ |  |
| Theorem 5.2 affine image of a multivariate normal | If $X \sim N(\mu,\Sigma)$ and $Y = a + B X$, then $Y \sim N(a + B\mu, B \Sigma B')$ |  |
| Theorem 5.3 properties of the multivariate normal | For $X \sim N(\mu,\Sigma)$: $\mathbb{E}[X] = \mu$, $\operatorname{Var}(X) = \Sigma$, uncorrelated subvectors are independent, affine images are normal, and the standard quadratic-form laws give $\chi^2$, non-central $\chi^2$, and $t/F$ consequences |  |
| Theorem 5.4 conditional law of the OLS coefficient vector | $\hat{\beta} \mid X \sim N\!\left(\beta, \sigma^2 (X'X)^{-1}\right)$ | [olsBeta_hasGaussianLaw_of_error](../../HansenEconometrics/Chapter5NormalRegression.lean#L65)<br><code>HasGaussianLaw (fun ω => olsBeta X (X *ᵥ β + e ω)) μ</code> |
| Theorem 5.5 Kinal (1980) moment existence | If $(Y,X)$ are jointly normal, then $\mathbb{E}\|\hat{\beta}\|^r < \infty$ if and only if $r < n-k+1$ |  |
| Theorem 5.6 conditional law of the OLS residual vector | $\hat{e} \mid X \sim N(0,\sigma^2 M)$ and $\hat{e}$ is independent of $\hat{\beta}$ | [residual_hasGaussianLaw_of_error](../../HansenEconometrics/Chapter5NormalRegression.lean#L94)<br><code>HasGaussianLaw (fun ω => residual X (X *ᵥ β + e ω)) μ</code> |
| Residual variance estimator | $s^2 = \hat{e}' \hat{e} / (n-k)$ | [olsResidualVarianceEstimator](../../HansenEconometrics/Chapter5NormalRegression.lean#L20)<br><code>olsResidualVarianceEstimator X y := dotProduct (annihilatorMatrix X *ᵥ y) (annihilatorMatrix X *ᵥ y) / (Fintype.card n - Fintype.card k : ℝ)</code> |
| Residual variance under the linear model | $s^2 = (M e)' (M e) / (n-k)$ | [olsResidualVarianceEstimator_linear_model](../../HansenEconometrics/Chapter5NormalRegression.lean#L31)<br><code>olsResidualVarianceEstimator X (X *ᵥ β + e) = dotProduct (annihilatorMatrix X *ᵥ e) (annihilatorMatrix X *ᵥ e) / (Fintype.card n - Fintype.card k : ℝ)</code> |
| Residual quadratic form identity | $\hat{e}' \hat{e} = e' M e$ | [residual_quadratic_form_of_linear_model](../../HansenEconometrics/Chapter5NormalRegression.lean#L43)<br><code>dotProduct (annihilatorMatrix X *ᵥ e) (annihilatorMatrix X *ᵥ e) = e ⬝ᵥ (annihilatorMatrix X) *ᵥ e</code> |
| Theorem 5.7 residual variance estimator distribution | $\dfrac{(n-k)s^2}{\sigma^2} \sim \chi^2_{n-k}$ and $s^2$ is independent of $\hat{\beta}$ |  |
| Theorem 5.8 exact $t$ statistic law | $T = \dfrac{\hat{\beta}_j - \beta_j}{\sqrt{s^2[(X'X)^{-1}]_{jj}}} \sim t_{n-k}$ |  |
| Theorem 5.9 regression-coefficient confidence interval | $\hat{C} = [\hat{\beta} - c\, s(\hat{\beta}), \hat{\beta} + c\, s(\hat{\beta})]$ with $c = F^{-1}(1-\alpha/2)$ satisfies $\mathbb{P}[\beta \in \hat{C}] = 1 - \alpha$ |  |
| Theorem 5.10 rule-of-thumb $95\%$ interval | If $n-k \ge 61$, then $\hat{C} = [\hat{\beta} - 2 s(\hat{\beta}), \hat{\beta} + 2 s(\hat{\beta})]$ has coverage probability at least $0.95$ |  |
| Theorem 5.11 error-variance confidence interval | $\hat{C} = \left[\dfrac{(n-k)s^2}{c_2}, \dfrac{(n-k)s^2}{c_1}\right]$ with $c_1 = F^{-1}(\alpha/2)$ and $c_2 = F^{-1}(1-\alpha/2)$ satisfies $\mathbb{P}[\sigma^2 \in \hat{C}] = 1 - \alpha$ |  |
| Theorem 5.12 classical $t$ test | Under $H_0 : \beta = \beta_0$, if $T = \dfrac{\hat{\beta} - \beta_0}{s(\hat{\beta})}$ and $c$ satisfies $\mathbb{P}(|t_{n-k}| \ge c) = \alpha$, then the test "reject $H_0$ if $|T| > c$" has significance level $\alpha$ |  |
| Theorem 5.13 likelihood-ratio / $F$-test layer | Under $H_0 : \beta_2 = 0$, if $F = \dfrac{(\tilde{\sigma}^2 - \hat{\sigma}^2)/q}{\hat{\sigma}^2/(n-k)}$, then $F \sim F_{q,n-k}$ and the test "reject $H_0$ if $F > c$" has significance level $\alpha$ when $\mathbb{P}(F_{q,n-k} \ge c) = \alpha$ |  |

## Notes

- Chapter 5 is only partially formalized. The current Lean layer provides the deterministic quadratic-
  form setup and the Gaussian-law bridge, but not yet the exact chi-square / $t$ / confidence-interval
  consequences.
- The LaTeX side now tracks the textbook theorem sequence more fully; the Lean side is only filled in
  where there is already an actual theorem or definition in the repo.
