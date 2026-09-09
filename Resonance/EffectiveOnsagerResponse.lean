import Resonance.ActualOnsagerRank
import Resonance.RealMatrixComplexification

/-! The original response descends exactly to eight effective coordinates;
this descent is used before compactness and quantitative comparison. -/
open scoped BigOperators
namespace Resonance.EffectiveOnsagerResponse
noncomputable section
set_option maxHeartbeats 800000
open Thermodynamics ActualOnsagerTensor ActualOnsagerPositive ActualOnsagerMatrix
open ActualOnsagerRank EffectiveGradientSpace RealMatrixComplexification

theorem quadratic_equal_of_kernel {I : Type*} [Fintype I] (M : Matrix I I ℝ)
    (hs : ∀i j,M i j=M j i) (x y : I→ℝ) (hz : M.mulVec (x-y)=0) :
    (∑i,x i*(M.mulVec x i))=∑i,y i*(M.mulVec y i) := by
  have he : M.mulVec x=M.mulVec y := by
    rw [Matrix.mulVec_sub] at hz
    exact sub_eq_zero.mp hz
  have hb := real_bilinear_symmetric M hs (x-y) y
  rw [hz] at hb
  simp only [Pi.zero_apply,mul_zero,Finset.sum_const_zero,Pi.sub_apply,
    sub_mul,Finset.sum_sub_distrib] at hb
  rw [he]
  exact sub_eq_zero.mp hb

theorem reconstruction_continuous : Continuous reconstruction := by
  apply continuous_pi
  intro i
  rcases i with ⟨j,k⟩
  fin_cases j <;> fin_cases k <;>
    simp [reconstruction,OnsagerGradientPolynomial.gradient] <;> fun_prop

theorem reconstruction_smul (a : ℝ) (p : Fin 8→ℝ) :
    reconstruction (a • p)=a • reconstruction p := by
  funext i
  rcases i with ⟨j,k⟩
  fin_cases j <;> fin_cases k <;>
    simp [reconstruction,OnsagerGradientPolynomial.gradient,smul_eq_mul,mul_add]

theorem quadratic_smul {R : ℝ} (hR : 0<R) {θ : Parameter}
    (hθ : θ∈positiveDomain R) (a : ℝ) (ξ : Index→ℝ) :
    quadraticResponse hR hθ (a • ξ)=a^2*quadraticResponse hR hθ ξ := by
  simp only [quadraticResponse,Pi.smul_apply,smul_eq_mul,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem actual_effective_response {R : ℝ} (hR : 0<R) {θ : Parameter}
    (hθ : θ∈positiveDomain R) (ξ : Index→ℝ) :
    quadraticResponse hR hθ ξ=quadraticResponse hR hθ (reconstruction (observation ξ)) := by
  have ho : observationLinear (ξ-reconstruction (observation ξ))=0 := by
    rw [map_sub]
    change observation ξ-observation (reconstruction (observation ξ))=0
    rw [observation_reconstruction,sub_self]
  have hk : ξ-reconstruction (observation ξ)∈(Matrix.toLin' (tensor hR hθ)).ker := by
    rw [actual_kernel_eq_effective_kernel]
    exact ho
  rw [quadratic_as_matrix_pairing,quadratic_as_matrix_pairing]
  exact quadratic_equal_of_kernel _ (tensor_reciprocity hR hθ) _ _ hk

theorem effective_response_zero_iff {R : ℝ} (hR : 0<R) {θ : Parameter}
    (hθ : θ∈positiveDomain R) (p : Fin 8→ℝ) :
    quadraticResponse hR hθ (reconstruction p)=0 ↔ p=0 := by
  rw [←actual_linear_kernel_iff,actual_kernel_eq_effective_kernel]
  change observation (reconstruction p)=0 ↔ p=0
  rw [observation_reconstruction]

theorem effective_response_positive {R : ℝ} (hR : 0<R) {θ : Parameter}
    (hθ : θ∈positiveDomain R) {p : Fin 8→ℝ} (hp : p≠0) :
    0<quadraticResponse hR hθ (reconstruction p) :=
  lt_of_le_of_ne (actual_tensor_positive hR hθ _) (Ne.symm (fun hz=>hp
    ((effective_response_zero_iff hR hθ p).mp hz)))

end
end Resonance.EffectiveOnsagerResponse
