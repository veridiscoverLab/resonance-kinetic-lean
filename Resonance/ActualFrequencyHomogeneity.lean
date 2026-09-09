import Resonance.MatrixHilbertDictionary
import Resonance.ActualNormalizedMatrices

/-! Exact frequency homogeneity of the original Euler and Onsager
symbols, before and after the Gram and complex Hilbert normalizations. -/
open Matrix
open scoped BigOperators
namespace Resonance.ActualFrequencyHomogeneity
noncomputable section
open Thermodynamics ActualEulerCoupling ActualFourierSymbol ActualNormalizedMatrices
open MatrixHilbertDictionary RealMatrixComplexification

theorem spatial_smul (R : ℝ) (θ : Parameter) (r : ℝ) (ell : Fin 3→ℝ) :
    spatialMatrix R θ (r • ell)=r • spatialMatrix R θ ell := by
  simp only [spatialMatrix,Pi.smul_apply,smul_eq_mul,Finset.smul_sum,smul_smul]

theorem symbol_smul {R : ℝ} (hR : 0 < R) {θ : Parameter}
    (hθ : θ∈positiveDomain R) (r : ℝ) (ell : Fin 3→ℝ) :
    symbol hR hθ (r • ell)=r^2 • symbol hR hθ ell := by
  ext a b
  simp only [Matrix.smul_apply,symbol_original_contraction,Pi.smul_apply,smul_eq_mul,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem normalized_euler_smul (R : ℝ) (θ : Parameter) (r : ℝ) (ell : Fin 3→ℝ) :
    normalizedEuler R θ (r • ell)=r • normalizedEuler R θ ell := by
  simp only [normalizedEuler,spatial_smul,Matrix.mul_smul,Matrix.smul_mul]

theorem normalized_damping_smul {R : ℝ} (hR : 0 < R) {θ : Parameter}
    (hθ : θ∈positiveDomain R) (r : ℝ) (ell : Fin 3→ℝ) :
    normalizedDamping hR hθ (r • ell)=r^2 • normalizedDamping hR hθ ell := by
  simp only [normalizedDamping,symbol_smul,Matrix.mul_smul,Matrix.smul_mul]

theorem operator_smul (r : ℝ) (M : Matrix (Fin 5) (Fin 5) ℝ) :
    operator (r • M)=(r : ℂ) • operator M := by
  have he : complexify (r • M)=(r : ℂ) • complexify M := by
    ext i j
    simp [complexify,Matrix.smul_apply,smul_eq_mul]
  unfold operator
  rw [he]
  exact map_smul (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin 5)) _ _

theorem spatial_zero (R : ℝ) (θ : Parameter) : spatialMatrix R θ 0=0 := by
  have hh := spatial_smul R θ 0 0
  simpa only [zero_smul] using hh

theorem symbol_zero {R : ℝ} (hR : 0 < R) {θ : Parameter}
    (hθ : θ∈positiveDomain R) : symbol hR hθ 0=0 := by
  have hh := symbol_smul hR hθ 0 0
  simpa only [zero_smul,zero_pow (by norm_num : (2 : ℕ)≠0)] using hh

end
end Resonance.ActualFrequencyHomogeneity
