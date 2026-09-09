import Resonance.ActualOnsagerTensor
import Resonance.ResponseFiniteAlgebra
import Resonance.CellSourceFaithfulness
import Resonance.BoundedMomentSum
import Resonance.CellVariationalPrinciple

/-! The full fifteen-dimensional quadratic response, including every
cross term, its variational maximum and its exact analytic null condition. -/
open MeasureTheory Set
open scoped ENNReal BigOperators
namespace Resonance.ActualOnsagerPositive
noncomputable section
open ResonantMeasure WeightedJointMeasure Thermodynamics ReferenceFrequencySpace
open ActualPairNormalization (cubeVolume)
open ReferenceMomentFunctionals PhysicalMomentProjection PhysicalFrequencyCoordinates PhysicalWeightedCoercivity
open PhysicalVariationalCell CellResponse BoundedCellSource ActualOnsagerTensor
open BoundedMomentSum ResponseFiniteAlgebra CellSourceFaithfulness CellVariationalPrinciple

def combinedDrive {R : ℝ} (hR : 0<R) {θ : Parameter} (hθ : θ∈positiveDomain R)
    (a : Index→ℝ) (k : E) : ℝ := ∑i,a i*drive hR hθ i k

theorem combinedDrive_memLp {R : ℝ} (hR : 0<R) {θ : Parameter}
    (hθ : θ∈positiveDomain R) (a : Index→ℝ) :
    MemLp (combinedDrive hR hθ a) ∞ (referenceMeasure R) :=
  bounded_sum_memLp (drive_memLp_top hR hθ) a

theorem combinedDrive_micro {R : ℝ} (hR : 0<R) {θ : Parameter}
    (hθ : θ∈positiveDomain R) (a : Index→ℝ) :
    projection hR hθ (boundedVector hR (combinedDrive_memLp hR hθ a))=0 :=
  micro_sum hR hθ (drive_memLp_top hR hθ) (drive_micro hR hθ) a

theorem combined_source {R : ℝ} (hR : 0<R) {θ : Parameter}
    (hθ : θ∈positiveDomain R) (a : Index→ℝ) :
    moment hR (combinedDrive_memLp hR hθ a)=∑i,a i • source hR hθ i :=
  moment_sum hR (drive_memLp_top hR hθ) a

def quadraticResponse {R : ℝ} (hR : 0<R) {θ : Parameter}
    (hθ : θ∈positiveDomain R) (a : Index→ℝ) : ℝ := ∑i,∑j,a i*tensor hR hθ i j*a j

theorem quadratic_as_response {R : ℝ} (hR : 0<R) {θ : Parameter}
    (hθ : θ∈positiveDomain R) (a : Index→ℝ) :
    quadraticResponse hR hθ a=response hR hθ
      (moment hR (combinedDrive_memLp hR hθ a)) (moment hR (combinedDrive_memLp hR hθ a)) := by
  rw [combined_source,response_finite_sum]
  rfl

theorem actual_tensor_positive {R : ℝ} (hR : 0<R) {θ : Parameter}
    (hθ : θ∈positiveDomain R) (a : Index→ℝ) : 0≤quadraticResponse hR hθ a := by
  rw [quadratic_as_response]
  exact response_nonnegative hR hθ _

theorem quadratic_actual_four_leg_form {R : ℝ} (hR : 0<R) {θ : Parameter}
    (hθ : θ∈positiveDomain R) (a : Index→ℝ) :
    quadraticResponse hR hθ a=physicalForm hR.le hθ
      (cell hR hθ (combinedDrive_memLp hR hθ a)) (cell hR hθ (combinedDrive_memLp hR hθ a)) := by
  rw [quadratic_as_response,response_as_form]
  rfl

theorem quadratic_zero_iff_drive_zero {R : ℝ} (hR : 0<R) {θ : Parameter}
    (hθ : θ∈positiveDomain R) (a : Index→ℝ) :
    quadraticResponse hR hθ a=0 ↔ combinedDrive hR hθ a=ᵐ[cubeVolume R]0 := by
  rw [quadratic_as_response]
  exact actual_response_zero_iff hR hθ _ (combinedDrive_micro hR hθ a)

theorem actual_tensor_variational_maximum {R : ℝ} (hR : 0<R) {θ : Parameter}
    (hθ : θ∈positiveDomain R) (a : Index→ℝ) (v : Micro hR hθ) :
    (2*(∫k,(v : Space R) k*combinedDrive hR hθ a k∂cubeVolume R)-physicalForm hR.le hθ v v
      ≤quadraticResponse hR hθ a) ∧
    (2*(∫k,(v : Space R) k*combinedDrive hR hθ a k∂cubeVolume R)-physicalForm hR.le hθ v v
      =quadraticResponse hR hθ a ↔ v=cell hR hθ (combinedDrive_memLp hR hθ a)) := by
  rw [quadratic_as_response]
  have hh := unique_variational_maximizer hR hθ (moment hR (combinedDrive_memLp hR hθ a)) v
  simpa only [objective,moment_apply] using hh

end
end Resonance.ActualOnsagerPositive
