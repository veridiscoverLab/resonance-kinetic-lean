import Resonance.ActualGramInverse
import Resonance.ActualSymbolUniform

/-! Symmetric normalization of the original Euler and collision matrices.
No matrix-valued constitutive law or normalization hypothesis is added. -/
open Matrix
open scoped BigOperators Matrix.Norms.Elementwise
namespace Resonance.ActualNormalizedMatrices
noncomputable section
open Thermodynamics EulerCoefficients ActualEulerCoupling ActualFourierSymbol
open ActualGramRoot ActualGramInverse ActualSymbolUniform

def normalizedEuler (R : ℝ) (θ : Parameter) (ell : Fin 3→ℝ) :
    Matrix (Fin 5) (Fin 5) ℝ :=
  (gramRoot R θ)⁻¹*spatialMatrix R θ ell*(gramRoot R θ)⁻¹

def normalizedDamping {R : ℝ} (hR : 0 < R) {θ : Parameter}
    (hθ : θ∈positiveDomain R) (ell : Fin 3→ℝ) : Matrix (Fin 5) (Fin 5) ℝ :=
  (gramRoot R θ)⁻¹*symbol hR hθ ell*(gramRoot R θ)⁻¹

theorem original_spatial_symmetric (R : ℝ) (θ : Parameter) (ell : Fin 3→ℝ) :
    (spatialMatrix R θ ell).IsHermitian := by
  ext i j
  change (spatialMatrix R θ ell j i)=spatialMatrix R θ ell i j
  simp only [spatialMatrix,Matrix.sum_apply,Matrix.smul_apply,smul_eq_mul]
  apply Finset.sum_congr rfl
  intro k _
  have hh : fluxMatrix R k θ j i=fluxMatrix R k θ i j := by
    simpa using congrFun (congrFun (fluxMatrix_isHermitian R k θ).eq i) j
  rw [hh]

theorem original_symbol_symmetric {R : ℝ} (hR : 0 < R) {θ : Parameter}
    (hθ : θ∈positiveDomain R) (ell : Fin 3→ℝ) : (symbol hR hθ ell).IsHermitian := by
  ext i j
  exact symbol_symmetric hR hθ ell j i

theorem original_normalized_euler_symmetric {R : ℝ} (hR : 0 < R) {θ : Parameter}
    (hθ : θ∈positiveDomain R) (ell : Fin 3→ℝ) : (normalizedEuler R θ ell).IsHermitian := by
  change (normalizedEuler R θ ell)ᴴ=normalizedEuler R θ ell
  simp only [normalizedEuler,Matrix.conjTranspose_mul,
    (original_inverse_symmetric hR hθ).eq,(original_spatial_symmetric R θ ell).eq]
  rw [Matrix.mul_assoc]

theorem original_normalized_damping_symmetric {R : ℝ} (hR : 0 < R) {θ : Parameter}
    (hθ : θ∈positiveDomain R) (ell : Fin 3→ℝ) : (normalizedDamping hR hθ ell).IsHermitian := by
  change (normalizedDamping hR hθ ell)ᴴ=normalizedDamping hR hθ ell
  simp only [normalizedDamping,Matrix.conjTranspose_mul,
    (original_inverse_symmetric hR hθ).eq,(original_symbol_symmetric hR hθ ell).eq]
  rw [Matrix.mul_assoc]

theorem original_spatial_continuous (R : ℝ) :
    Continuous (fun p : positiveDomain R×(Fin 3→ℝ)=>spatialMatrix R p.1 p.2) := by
  unfold spatialMatrix
  apply continuous_finset_sum
  intro j _
  have hj : Continuous (fun θ : positiveDomain R=>fluxMatrix R j θ) :=
    continuousOn_iff_continuous_restrict.mp (fluxMatrix_contDiffOn_finite R j 0).continuousOn
  exact ((continuous_apply j).comp continuous_snd).smul (hj.comp continuous_fst)

theorem original_normalized_euler_continuous {R : ℝ} (hR : 0 < R) :
    Continuous (fun p : positiveDomain R×(Fin 3→ℝ)=>normalizedEuler R p.1 p.2) :=
  ((original_inverse_continuous hR).comp continuous_fst |>.mul
    (original_spatial_continuous R)).mul ((original_inverse_continuous hR).comp continuous_fst)

theorem original_normalized_damping_continuous {R : ℝ} (hR : 0 < R) :
    Continuous (fun p : positiveDomain R×(Fin 3→ℝ)=>normalizedDamping hR p.1.property p.2) :=
  ((original_inverse_continuous hR).comp continuous_fst |>.mul
    (original_symbol_continuous hR)).mul ((original_inverse_continuous hR).comp continuous_fst)

end
end Resonance.ActualNormalizedMatrices
