import Resonance.ActualModeConjugacy

/-! All original spatial matrix slots, without replacing the fifteen-by-
fifteen response tensor by an independent diffusion matrix. -/
namespace Resonance.ActualSpatialMatrixSymbols
noncomputable section
open Thermodynamics MatrixHilbertDictionary RealMatrixComplexification
open ActualEulerCoupling ActualFourierSymbol ActualFrequencyHomogeneity ActualOnsagerTensor

theorem operator_sum {I : Type*} (S : Finset I) (M : I→Matrix (Fin 5) (Fin 5) ℝ) :
    operator (∑i∈S,M i)=∑i∈S,operator (M i) := by
  have he : complexify (∑i∈S,M i)=∑i∈S,complexify (M i) := by
    ext a b
    simp only [complexify,Matrix.sum_apply,Complex.ofReal_sum]
  unfold operator
  rw [he,map_sum]

def block {R : ℝ} (hR : 0<R) {θ : Parameter} (hθ : θ∈positiveDomain R)
    (i j : Fin 3) : Matrix (Fin 5) (Fin 5) ℝ :=
  fun a b=>tensor hR hθ (i,a) (j,b)

theorem symbol_blocks {R : ℝ} (hR : 0<R) {θ : Parameter}
    (hθ : θ∈positiveDomain R) (ell : Fin 3→ℝ) :
    symbol hR hθ ell=∑i,∑j,(ell i*ell j) • block hR hθ i j := by
  ext a b
  simp only [symbol_original_contraction,Matrix.sum_apply,Matrix.smul_apply,smul_eq_mul,block]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem spatial_operator {R : ℝ} (Rθ : Parameter) (ell : Fin 3→ℝ) :
    operator (spatialMatrix R Rθ ell)=
      ∑j,(ell j:ℂ) • operator (EulerCoefficients.fluxMatrix R j Rθ) := by
  rw [spatialMatrix,operator_sum]
  simp only [operator_smul]

theorem diffusion_operator {R : ℝ} (hR : 0<R) {θ : Parameter}
    (hθ : θ∈positiveDomain R) (ell : Fin 3→ℝ) :
    operator (symbol hR hθ ell)=
      ∑i,∑j,((ell i:ℂ)*(ell j:ℂ)) • operator (block hR hθ i j) := by
  rw [symbol_blocks,operator_sum]
  simp only [operator_sum,operator_smul,Complex.ofReal_mul]

end
end Resonance.ActualSpatialMatrixSymbols
