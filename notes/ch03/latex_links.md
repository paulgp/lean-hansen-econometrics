# Chapter 3 LaTeX / Lean Crosswalk

This file maps Chapter 3 textbook statements to the current Lean formalization.

Conventions:
- All links in this file are relative.
- The LaTeX column aims to stay close to Hansen's notation.
- The Lean column gives the linked theorem or definition name plus the core conclusion.
- Blank Lean cells mark statements that are still pending.

## Links

- [Inventory](./inventory.md)
- [Hansen excerpt](./ch3_excerpt.txt)
- [Least-squares algebra file](../../HansenEconometrics/Chapter3LeastSquaresAlgebra.lean)
- [Projection file](../../HansenEconometrics/Chapter3Projections.lean)
- [FWL file](../../HansenEconometrics/Chapter3FWL.lean)

## Crosswalk

| Textbook result | LaTeX | Lean theorem |
| --- | --- | --- |
| Theorem 3.1 objective-level argmin statement | $\hat{\beta} = \arg\min_b (Y - X b)'(Y - X b)$ |  |
| Definition 3.1 sum of squared errors | $S(b) = (Y - X b)'(Y - X b)$ | [sumSquaredErrors](../../HansenEconometrics/Chapter3LeastSquaresAlgebra.lean#L16)<br><code>sumSquaredErrors X y b := (y - X *ᵥ b) ⬝ᵥ (y - X *ᵥ b)</code> |
| Theorem 3.2 closed-form OLS coefficient | $\hat{\beta} = (X'X)^{-1} X' Y$ | [olsBeta](../../HansenEconometrics/Chapter3LeastSquaresAlgebra.lean#L20)<br><code>olsBeta X y := (⅟ (Xᵀ * X)) *ᵥ (Xᵀ *ᵥ y)</code> |
| Theorem 3.2 normal equations | $X' \hat{e} = 0$ | [normal_equations](../../HansenEconometrics/Chapter3LeastSquaresAlgebra.lean#L32)<br><code>Xᵀ *ᵥ residual X y = 0</code> |
| Equation (3.17) residuals sum to zero with an intercept | $\iota \in \operatorname{col}(X) \Longrightarrow \sum_i \hat{e}_i = 0$ | [residual_sum_zero_of_one_mem_colspan](../../HansenEconometrics/Chapter3LeastSquaresAlgebra.lean#L84)<br><code>∑ i, residual X y i = 0</code> |
| Section 3.11 hat matrix | $P = X (X'X)^{-1} X'$ | [hatMatrix](../../HansenEconometrics/Chapter3Projections.lean#L24)<br><code>hatMatrix X := X * ⅟ (Xᵀ * X) * Xᵀ</code> |
| Section 3.12 annihilator matrix | $M = I - P$ | [annihilatorMatrix](../../HansenEconometrics/Chapter3Projections.lean#L28)<br><code>annihilatorMatrix X := 1 - hatMatrix X</code> |
| Theorem 3.3.1 hat-matrix symmetry | $P' = P$ | [hatMatrix_transpose](../../HansenEconometrics/Chapter3Projections.lean#L40)<br><code>(hatMatrix X)ᵀ = hatMatrix X</code> |
| Theorem 3.3.2 hat-matrix idempotence | $P^2 = P$ | [hatMatrix_idempotent](../../HansenEconometrics/Chapter3Projections.lean#L104)<br><code>hatMatrix X * hatMatrix X = hatMatrix X</code> |
| Equation (3.21) annihilator kills the regressors | $M X = 0$ | [annihilator_mul_X](../../HansenEconometrics/Chapter3Projections.lean#L90)<br><code>annihilatorMatrix X * X = 0</code> |
| Equation (3.22) trace of the annihilator | $\operatorname{tr}(M) = n - k$ | [annihilatorMatrix_trace](../../HansenEconometrics/Chapter3Projections.lean#L145)<br><code>Matrix.trace (annihilatorMatrix X) = (Fintype.card n : ℝ) - Fintype.card k</code> |
| Equation (3.23) residual representation | $\hat{e} = M Y$ | [residual_eq_annihilator_mul_y](../../HansenEconometrics/Chapter3Projections.lean#L242)<br><code>residual X y = annihilatorMatrix X *ᵥ y</code> |
| Section 3.14 fitted values and residuals are orthogonal | $\hat{Y}' \hat{e} = 0$ | [fitted_dot_residual](../../HansenEconometrics/Chapter3Projections.lean#L249)<br><code>fitted X y ⬝ᵥ residual X y = 0</code> |
| Section 3.14 Pythagorean decomposition | $Y'Y = \hat{Y}'\hat{Y} + \hat{e}'\hat{e}$ | [fitted_residual_pythagorean](../../HansenEconometrics/Chapter3Projections.lean#L259)<br><code>y ⬝ᵥ y = fitted X y ⬝ᵥ fitted X y + residual X y ⬝ᵥ residual X y</code> |
| Theorem 3.4 partitioned coefficient formulae | $\hat{\beta}_1,\hat{\beta}_2$ as functions of partitioned moments |  |
| Theorem 3.5 coefficient equivalence | $\hat{\beta}_2 = (X_2' M_1 X_2)^{-1} X_2' M_1 Y$ | [fromColsRightBeta_eq_fwlBeta](../../HansenEconometrics/Chapter3FWL.lean#L147)<br><code>fromColsRightBeta X₁ X₂ y = fwlBeta X₁ X₂ y</code> |
| Theorem 3.5 residual equivalence | $\hat{e}_{\text{full}} = M_{M_1 X_2} M_1 Y$ | [fwl_residual_eq_full_residual](../../HansenEconometrics/Chapter3FWL.lean#L163)<br><code>residual (residualizedRegressors X₁ X₂) (annihilatorMatrix X₁ *ᵥ y) = residual (Matrix.fromCols X₁ X₂) y</code> |

## Notes

- Theorem 3.1 and Theorem 3.4 are still intentionally blank: they are the main remaining Chapter 3
  theorem labels not yet wrapped in the current Lean layer.
- Several Lean helper results in the projection file are stronger than the textbook labels because
  they package reusable matrix facts such as rank and Hermitian structure.
