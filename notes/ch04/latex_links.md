# Chapter 4 LaTeX / Lean Crosswalk

This file maps Chapter 4 textbook statements to the current Lean formalization.

Conventions:
- All links in this file are relative.
- The Lean column gives the linked theorem or definition name plus the core conclusion.
- Blank Lean cells mark statements that are still pending or deliberately deferred.

## Links

- [Inventory](./inventory.md)
- [Hansen excerpt](./ch4_excerpt.txt)
- [Lean file](../../HansenEconometrics/Chapter4LeastSquaresRegression.lean)

## Crosswalk

| Textbook result | LaTeX | Lean theorem |
| --- | --- | --- |
| Equation (4.6) OLS decomposition | $\hat{\beta} = \beta + (X'X)^{-1} X' e$ | [olsBeta_linear_decomposition](../../HansenEconometrics/Chapter4LeastSquaresRegression.lean#L16)<br><code>olsBeta X (X *ᵥ β + e) = β + (⅟ (Xᵀ * X)) *ᵥ (Xᵀ *ᵥ e)</code> |
| Orthogonal-error specialization | $X' e = 0 \Longrightarrow \hat{\beta} = \beta$ | [olsBeta_eq_of_regressors_orthogonal_error](../../HansenEconometrics/Chapter4LeastSquaresRegression.lean#L29)<br><code>olsBeta X (X *ᵥ β + e) = β</code> |
| Fitted values in the linear model | $\hat{Y} = X \beta + P e$ | [fitted_linear_model](../../HansenEconometrics/Chapter4LeastSquaresRegression.lean#L37)<br><code>fitted X (X *ᵥ β + e) = X *ᵥ β + hatMatrix X *ᵥ e</code> |
| Residuals in the linear model | $\hat{e} = M e$ | [residual_linear_model](../../HansenEconometrics/Chapter4LeastSquaresRegression.lean#L45)<br><code>residual X (X *ᵥ β + e) = annihilatorMatrix X *ᵥ e</code> |
| Theorem 4.1 conditional unbiasedness | $\mathbb{E}[\hat{\beta} \mid X] = \beta$ | [ols_condExp_eq_beta](../../HansenEconometrics/Chapter4LeastSquaresRegression.lean#L243)<br><code>μ[fun ω => olsBeta X (X *ᵥ β + e ω) &#124; m] =ᵐ[μ] fun _ => β</code> |
| Theorem 4.1 unconditional unbiasedness | $\mathbb{E}[\hat{\beta}] = \beta$ | [ols_integral_eq_beta](../../HansenEconometrics/Chapter4LeastSquaresRegression.lean#L292)<br><code>∫ ω, olsBeta X (X *ᵥ β + e ω) ∂μ = β</code> |
| Theorem 4.2 conditional covariance formula | $\operatorname{Var}(\hat{\beta} \mid X) = (X'X)^{-1} X' D X (X'X)^{-1}$ | [olsConditionalVarianceMatrix](../../HansenEconometrics/Chapter4LeastSquaresRegression.lean#L55)<br><code>olsConditionalVarianceMatrix X D := ⅟ (Xᵀ * X) * Xᵀ * D * X * ⅟ (Xᵀ * X)</code><br>[ols_condExp_centered_mul_eq_variance_matrix](../../HansenEconometrics/Chapter4LeastSquaresRegression.lean#L432)<br><code>μ[fun ω => Matrix.of fun i j => centered β̂ ω i * centered β̂ ω j &#124; m] =ᵐ[μ] fun _ => olsConditionalVarianceMatrix X D</code> |
| Theorem 4.2 unconditional covariance identity | $\mathbb{E}[(\hat{\beta} - \beta)(\hat{\beta} - \beta)'] = \mathbb{E}[\operatorname{Var}(\hat{\beta} \mid X)]$ | [ols_integral_centered_mul_eq_variance_matrix](../../HansenEconometrics/Chapter4LeastSquaresRegression.lean#L504)<br><code>∫ ω, Matrix.of fun i j => centered β̂ ω i * centered β̂ ω j ∂μ = olsConditionalVarianceMatrix X D</code> |
| Theorem 4.2 homoskedastic simplification | $\operatorname{Var}(\hat{\beta} \mid X) = \sigma^2 (X'X)^{-1}$ | [olsConditionalVarianceMatrix_homoskedastic](../../HansenEconometrics/Chapter4LeastSquaresRegression.lean#L84)<br><code>olsConditionalVarianceMatrix X (σ2 • 1) = σ2 • ⅟ (Xᵀ * X)</code> |
| Gauss-Markov lower bound | $\operatorname{Var}(\tilde{\beta} \mid X) - \operatorname{Var}(\hat{\beta} \mid X) \succeq 0$ | [gaussMarkov_variance_gap_posSemidef](../../HansenEconometrics/Chapter4LeastSquaresRegression.lean#L111)<br><code>(Aᵀ * A - ⅟ (Xᵀ * X)).PosSemidef</code> |
| GLS coefficient | $\hat{\beta}_{GLS} = (X' \Omega^{-1} X)^{-1} X' \Omega^{-1} Y$ | [glsBeta](../../HansenEconometrics/Chapter4LeastSquaresRegression.lean#L577)<br><code>glsBeta X Ω y := (⅟ (Xᵀ * Ω⁻¹ * X)) *ᵥ (Xᵀ *ᵥ (Ω⁻¹ *ᵥ y))</code> |
| GLS decomposition | $\hat{\beta}_{GLS} = \beta + (X' \Omega^{-1} X)^{-1} X' \Omega^{-1} e$ | [glsBeta_linear_decomposition](../../HansenEconometrics/Chapter4LeastSquaresRegression.lean#L583)<br><code>glsBeta X Ω (X *ᵥ β + e) = β + (⅟ (Xᵀ * Ω⁻¹ * X)) *ᵥ (Xᵀ *ᵥ (Ω⁻¹ *ᵥ e))</code> |
| Generalized Gauss-Markov lower bound | weighted variance gap is positive semidefinite | [generalizedGaussMarkov_variance_gap_posSemidef](../../HansenEconometrics/Chapter4LeastSquaresRegression.lean#L608)<br><code>(Aᵀ * Ω * A - ⅟ (Xᵀ * Ω⁻¹ * X)).PosSemidef</code> |
| White HC0 covariance estimator | $\hat{V}_{HC0} = (X'X)^{-1} X' \operatorname{diag}(\hat{e}_i^2) X (X'X)^{-1}$ | [olsHuberWhiteVarianceEstimator](../../HansenEconometrics/Chapter4LeastSquaresRegression.lean#L65)<br><code>olsHuberWhiteVarianceEstimator X y := olsConditionalVarianceMatrix X (Matrix.diagonal fun i => residual X y i ^ 2)</code> |
| HC1 covariance estimator | $\hat{V}_{HC1} = \frac{n}{n-k} \hat{V}_{HC0}$ | [olsHuberWhiteHC1VarianceEstimator](../../HansenEconometrics/Chapter4LeastSquaresRegression.lean#L70)<br><code>olsHuberWhiteHC1VarianceEstimator X y := ((n : ℝ) / (n - k : ℝ)) • olsHuberWhiteVarianceEstimator X y</code> |
| Residual variance estimators / HC2 / HC3 / clustered covariance | textbook estimator layer |  |

## Notes

- Chapter 4 has strong deterministic and conditional-expectation coverage already, so this file is
  mostly a map from Hansen's notation into the matrix-valued Lean API.
- The covariance-estimator layer is intentionally incomplete: HC2 / HC3 and clustered covariance are
  still deferred.
