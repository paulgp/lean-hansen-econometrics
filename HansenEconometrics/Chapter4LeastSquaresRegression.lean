import Mathlib
import HansenEconometrics.Basic
import HansenEconometrics.Chapter3Projections

open scoped Matrix

namespace HansenEconometrics

open Matrix

variable {n k : Type*}
variable [Fintype n] [Fintype k] [DecidableEq k]

/-- Hansen equation (4.6): OLS equals the true coefficient plus the projected error. -/
theorem olsBeta_linear_decomposition
    (X : Matrix n k ℝ) (β : k → ℝ) (e : n → ℝ) [Invertible (Xᵀ * X)] :
    olsBeta X (X *ᵥ β + e) = β + (⅟ (Xᵀ * X)) *ᵥ (Xᵀ *ᵥ e) := by
  unfold olsBeta
  rw [Matrix.mulVec_add]
  have hxx : Xᵀ *ᵥ (X *ᵥ β) = (Xᵀ * X) *ᵥ β := by
    rw [Matrix.mulVec_mulVec]
  rw [hxx, Matrix.mulVec_add]
  rw [Matrix.mulVec_mulVec β (⅟ (Xᵀ * X)) (Xᵀ * X)]
  rw [invOf_mul_self]
  simp

/-- If the model error is orthogonal to the regressors, the closed-form OLS coefficient is `β`. -/
theorem olsBeta_eq_of_regressors_orthogonal_error
    (X : Matrix n k ℝ) (β : k → ℝ) (e : n → ℝ) [Invertible (Xᵀ * X)]
    (he : Xᵀ *ᵥ e = 0) :
    olsBeta X (X *ᵥ β + e) = β := by
  rw [olsBeta_linear_decomposition, he]
  simp

/-- In the finite-sample linear model, fitted values equal signal plus projected error. -/
theorem fitted_linear_model
    (X : Matrix n k ℝ) (β : k → ℝ) (e : n → ℝ) [Invertible (Xᵀ * X)] :
    fitted X (X *ᵥ β + e) = X *ᵥ β + hatMatrix X *ᵥ e := by
  unfold fitted
  rw [olsBeta_linear_decomposition, Matrix.mulVec_add]
  rw [← hat_mul_y_eq_closed_form_fit]

/-- In the finite-sample linear model, OLS residuals are the annihilator applied to the error. -/
theorem residual_linear_model
    (X : Matrix n k ℝ) (β : k → ℝ) (e : n → ℝ) [DecidableEq n]
    [Invertible (Xᵀ * X)] :
    residual X (X *ᵥ β + e) = annihilatorMatrix X *ᵥ e := by
  unfold residual annihilatorMatrix
  rw [fitted_linear_model, Matrix.sub_mulVec, Matrix.one_mulVec]
  ext i
  simp [sub_eq_add_neg, add_assoc, add_comm]

/-- Hansen Theorem 4.2 matrix core: conditional covariance formula for OLS. -/
noncomputable def olsConditionalVarianceMatrix
    (X : Matrix n k ℝ) (D : Matrix n n ℝ) [Invertible (Xᵀ * X)] : Matrix k k ℝ :=
  ⅟ (Xᵀ * X) * Xᵀ * D * X * ⅟ (Xᵀ * X)

/-- The covariance formula written as `Aᵀ D A`, where `A = X (XᵀX)⁻¹`. -/
theorem olsConditionalVarianceMatrix_eq_Atranspose_D_A
    (X : Matrix n k ℝ) (D : Matrix n n ℝ) [Invertible (Xᵀ * X)] :
    (X * ⅟ (Xᵀ * X))ᵀ * D * (X * ⅟ (Xᵀ * X)) =
      olsConditionalVarianceMatrix X D := by
  unfold olsConditionalVarianceMatrix
  rw [Matrix.transpose_mul, inv_gram_transpose]
  simp [Matrix.mul_assoc]

/-- Hansen Theorem 4.2 homoskedastic simplification: `D = σ² I`. -/
theorem olsConditionalVarianceMatrix_homoskedastic
    (X : Matrix n k ℝ) (σ2 : ℝ) [DecidableEq n] [Invertible (Xᵀ * X)] :
    olsConditionalVarianceMatrix X (σ2 • (1 : Matrix n n ℝ)) =
      σ2 • ⅟ (Xᵀ * X) := by
  unfold olsConditionalVarianceMatrix
  rw [Matrix.mul_assoc (⅟ (Xᵀ * X) * Xᵀ) (σ2 • (1 : Matrix n n ℝ)) X]
  simp [Matrix.mul_assoc]

/-- Deterministic core of the Gauss-Markov theorem: the variance-gap matrix is positive semidefinite. -/
theorem gaussMarkov_variance_gap_posSemidef
    (X A : Matrix n k ℝ) [Invertible (Xᵀ * X)]
    (hAX : Aᵀ * X = (1 : Matrix k k ℝ)) :
    (Aᵀ * A - ⅟ (Xᵀ * X)).PosSemidef := by
  let C : Matrix k n ℝ := Aᵀ - ⅟ (Xᵀ * X) * Xᵀ
  have hgap : C * Cᵀ = Aᵀ * A - ⅟ (Xᵀ * X) := by
    have hXA : Xᵀ * A = (1 : Matrix k k ℝ) := by
      simpa using congrArg Matrix.transpose hAX
    dsimp [C]
    rw [Matrix.transpose_sub, Matrix.transpose_mul, Matrix.transpose_transpose, inv_gram_transpose]
    rw [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub]
    have h1 : Aᵀ * (X * ⅟ (Xᵀ * X)) = ⅟ (Xᵀ * X) := by
      calc
        Aᵀ * (X * ⅟ (Xᵀ * X)) = (Aᵀ * X) * ⅟ (Xᵀ * X) := by rw [Matrix.mul_assoc]
        _ = 1 * ⅟ (Xᵀ * X) := by rw [hAX]
        _ = ⅟ (Xᵀ * X) := by simp
    have h2' : (Xᵀ * X)⁻¹ - (Xᵀ * X)⁻¹ * (Xᵀ * (X * (Xᵀ * X)⁻¹)) = 0 := by
      have hcancel : Xᵀ * (X * (Xᵀ * X)⁻¹) = (1 : Matrix k k ℝ) := by
        rw [← Matrix.mul_assoc]
        simpa using (mul_invOf_self (Xᵀ * X))
      rw [hcancel]
      simp
    have h1' : Aᵀ * (X * (Xᵀ * X)⁻¹) = (Xᵀ * X)⁻¹ := by
      simpa using h1
    simp [Matrix.transpose_transpose, Matrix.mul_assoc, hXA]
    rw [h1', h2']
    abel_nf
  have hpsd : (C * Cᵀ).PosSemidef := by
    simpa [Matrix.conjTranspose, Matrix.transpose_transpose] using
      (Matrix.posSemidef_self_mul_conjTranspose C)
  simpa [hgap] using hpsd

/-- Generalized least squares estimator with weight matrix `Ω⁻¹`. -/
noncomputable def glsBeta
    (X : Matrix n k ℝ) (Ω : Matrix n n ℝ) (y : n → ℝ)
    [DecidableEq n] [Invertible Ω] [Invertible (Xᵀ * ⅟Ω * X)] : k → ℝ :=
  (⅟ (Xᵀ * ⅟Ω * X)) *ᵥ (Xᵀ *ᵥ ((⅟Ω) *ᵥ y))

/-- GLS equals the true coefficient plus the weighted projected error. -/
theorem glsBeta_linear_decomposition
    (X : Matrix n k ℝ) (Ω : Matrix n n ℝ) (β : k → ℝ) (e : n → ℝ)
    [DecidableEq n] [Invertible Ω] [Invertible (Xᵀ * ⅟Ω * X)] :
    glsBeta X Ω (X *ᵥ β + e) = β + (⅟ (Xᵀ * ⅟Ω * X)) *ᵥ (Xᵀ *ᵥ ((⅟Ω) *ᵥ e)) := by
  unfold glsBeta
  rw [Matrix.mulVec_add, Matrix.mulVec_add]
  have hmain : Xᵀ *ᵥ ((⅟Ω) *ᵥ (X *ᵥ β)) = (Xᵀ * ⅟Ω * X) *ᵥ β := by
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mul_assoc]
  rw [hmain]
  rw [Matrix.mulVec_add]
  rw [Matrix.mulVec_mulVec β (⅟ (Xᵀ * ⅟Ω * X)) (Xᵀ * ⅟Ω * X)]
  rw [invOf_mul_self]
  simp

/-- If the GLS-weighted error is orthogonal to the regressors, GLS recovers `β`. -/
theorem glsBeta_eq_of_weighted_regressors_orthogonal_error
    (X : Matrix n k ℝ) (Ω : Matrix n n ℝ) (β : k → ℝ) (e : n → ℝ)
    [DecidableEq n] [Invertible Ω] [Invertible (Xᵀ * ⅟Ω * X)]
    (he : Xᵀ *ᵥ ((⅟Ω) *ᵥ e) = 0) :
    glsBeta X Ω (X *ᵥ β + e) = β := by
  rw [glsBeta_linear_decomposition, he]
  simp

end HansenEconometrics
