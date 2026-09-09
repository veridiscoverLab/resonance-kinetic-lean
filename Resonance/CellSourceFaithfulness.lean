import Resonance.BoundedCellSource
import Resonance.CellResponse

/-! No bounded drive is lost by the variational pairing on the original
weighted space. This pays the analytic zero-response interface. -/
open MeasureTheory Set
open scoped ENNReal
namespace Resonance.CellSourceFaithfulness
noncomputable section
set_option maxHeartbeats 800000
open ResonantMeasure WeightedJointMeasure Thermodynamics ReferenceFrequencySpace
open ActualPairNormalization (cubeVolume)
open ReferenceMomentFunctionals PhysicalMomentProjection PhysicalProjectionKernel
open PhysicalFrequencyCoordinates PhysicalWeightedCoercivity PhysicalVariationalCell
open BoundedCellSource CellResponse

theorem bounded_square_integrable {R : ℝ} (hR : 0<R) {F : E→ℝ}
    (hF : MemLp F ∞ (referenceMeasure R)) : Integrable (fun k=>F k^2) (cubeVolume R) := by
  apply (weighted_moment_integrable hR hF (boundedVector hR hF)).congr
  filter_upwards [boundedVector_ae hR hF] with k hk
  rw [hk,pow_two]

theorem source_zero_iff {R : ℝ} (hR : 0<R) {F : E→ℝ}
    (hF : MemLp F ∞ (referenceMeasure R)) :
    moment hR hF=0 ↔ F=ᵐ[cubeVolume R]0 := by
  constructor
  · intro hz
    have he : (∫k,F k^2∂cubeVolume R)=0 := by
      have hh := congrArg (fun s : Space R→L[ℝ]ℝ=>s (boundedVector hR hF)) hz
      change moment hR hF (boundedVector hR hF)=(0 : Space R→L[ℝ]ℝ) (boundedVector hR hF) at hh
      rw [moment_apply,ContinuousLinearMap.zero_apply] at hh
      rw [←hh]
      apply integral_congr_ae
      filter_upwards [boundedVector_ae hR hF] with k hk
      rw [hk,pow_two]
    have ha := (integral_eq_zero_iff_of_nonneg_ae
      (ae_of_all (cubeVolume R) fun k=>sq_nonneg (F k)) (bounded_square_integrable hR hF)).mp he
    filter_upwards [ha] with k hk
    exact sq_eq_zero_iff.mp hk
  · intro hz
    apply ContinuousLinearMap.ext
    intro v
    rw [moment_apply,ContinuousLinearMap.zero_apply]
    apply integral_eq_zero_of_ae
    filter_upwards [hz] with k hk
    simp only [hk,Pi.zero_apply,mul_zero]

theorem micro_cell_zero_iff_source {R : ℝ} (hR : 0<R) {θ : Parameter}
    (hθ : θ∈positiveDomain R) {F : E→ℝ} (hF : MemLp F ∞ (referenceMeasure R))
    (hQ : projection hR hθ (boundedVector hR hF)=0) :
    cell hR hθ hF=0 ↔ moment hR hF=0 := by
  constructor
  · intro hz
    apply ContinuousLinearMap.ext
    intro v
    have he := solve_full_pairing hR hθ _ (micro_source_annihilates_kernel hR hθ hF hQ) v
    change physicalForm hR.le hθ (cell hR hθ hF) v=moment hR hF v at he
    rw [hz] at he
    simpa only [Submodule.coe_zero,physicalForm,map_zero,inner_zero_left] using he.symm
  · intro hz
    symm
    apply solve_unique hR hθ
    intro v
    simp only [hz,Submodule.coe_zero,physicalForm,map_zero,inner_zero_left,
      ContinuousLinearMap.zero_apply]

theorem actual_response_zero_iff {R : ℝ} (hR : 0<R) {θ : Parameter}
    (hθ : θ∈positiveDomain R) {F : E→ℝ} (hF : MemLp F ∞ (referenceMeasure R))
    (hQ : projection hR hθ (boundedVector hR hF)=0) :
    response hR hθ (moment hR hF) (moment hR hF)=0 ↔ F=ᵐ[cubeVolume R]0 := by
  rw [response_zero_iff]
  exact (micro_cell_zero_iff_source hR hθ hF hQ).trans (source_zero_iff hR hF)

end
end Resonance.CellSourceFaithfulness
