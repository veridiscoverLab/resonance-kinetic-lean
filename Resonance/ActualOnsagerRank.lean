import Resonance.ActualOnsagerNullDirections
import Resonance.ActualOnsagerMatrix
import Resonance.EffectiveGradientSpace

/-! Exact kernel dimension and rank of the original fifteen-by-fifteen
Onsager tensor, by its proved physical null-space classification. -/
namespace Resonance.ActualOnsagerRank
noncomputable section
open ResonantMeasure WeightedJointMeasure Thermodynamics
open ActualOnsagerTensor ActualOnsagerMatrix ActualOnsagerNullDirections
open OnsagerGradientPolynomial EffectiveGradientSpace

theorem actual_kernel_eq_effective_kernel {R : ℝ} (hR : 0<R) {θ : Parameter}
    (hθ : θ∈positiveDomain R) :
    (Matrix.toLin' (tensor hR hθ)).ker=observationLinear.ker := by
  ext ξ
  change ξ∈(Matrix.toLin' (tensor hR hθ)).ker ↔ observation ξ=0
  have hh := (actual_linear_kernel_iff hR hθ
      (gradient (fun j=>ξ (j,0)) (fun j l=>ξ (j,l.castSucc.succ)) (fun j=>ξ (j,4)))).trans
    ((actual_null_directions hR hθ _ _ _).trans
      (observation_gradient_zero_iff (fun j=>ξ (j,0)) _ _).symm)
  simpa only [gradient_exhaustive] using hh

theorem actual_kernel_dimension {R : ℝ} (hR : 0<R) {θ : Parameter}
    (hθ : θ∈positiveDomain R) : Module.finrank ℝ (Matrix.toLin' (tensor hR hθ)).ker=7 := by
  rw [actual_kernel_eq_effective_kernel]
  exact kernel_finrank

theorem actual_range_dimension {R : ℝ} (hR : 0<R) {θ : Parameter}
    (hθ : θ∈positiveDomain R) : Module.finrank ℝ (Matrix.toLin' (tensor hR hθ)).range=8 := by
  have hh := (Matrix.toLin' (tensor hR hθ)).finrank_range_add_finrank_ker
  rw [actual_kernel_dimension,ambient_finrank] at hh
  omega

theorem actual_tensor_rank {R : ℝ} (hR : 0<R) {θ : Parameter}
    (hθ : θ∈positiveDomain R) : (tensor hR hθ).rank=8 :=
  actual_range_dimension hR hθ

end
end Resonance.ActualOnsagerRank
