import Resonance.ActualOnsagerPositive
import Resonance.ProjectedDriveKernel

/-! The actual response null condition is transported to the original
collision-invariant equation before any polynomial coefficient calculation. -/
open MeasureTheory Set
open scoped ENNReal BigOperators
namespace Resonance.ActualOnsagerKernelBridge
noncomputable section
set_option maxHeartbeats 800000
open ResonantMeasure WeightedJointMeasure Thermodynamics ReferenceFrequencySpace
open ActualPairNormalization (cubeVolume)
open ReferenceMomentFunctionals PhysicalMomentProjection PhysicalProjectionKernel
open PhysicalFrequencyCoordinates PhysicalWeightedCoercivity
open BoundedCellSource BoundedMicroProjection BoundedMomentSum ProjectedDriveKernel
open ActualOnsagerTensor ActualOnsagerPositive

def rawCombination (θ : Parameter) (a : Index→ℝ) (k : E) : ℝ := ∑i,a i*rawDrive θ i k

theorem rawCombination_memLp {R : ℝ} {θ : Parameter}
    (hθ : θ∈positiveDomain R) (a : Index→ℝ) :
    MemLp (rawCombination θ a) ∞ (referenceMeasure R) :=
  bounded_sum_memLp (rawDrive_memLp_top hθ) a

theorem drive_vector {R : ℝ} (hR : 0<R) {θ : Parameter}
    (hθ : θ∈positiveDomain R) (i : Index) :
    boundedVector hR (drive_memLp_top hR hθ i)=boundedVector hR (rawDrive_memLp_top hθ i)-
      projection hR hθ (boundedVector hR (rawDrive_memLp_top hθ i)) :=
  projectDrive_vector hR hθ (rawDrive_memLp_top hθ i)

theorem combined_vector {R : ℝ} (hR : 0<R) {θ : Parameter}
    (hθ : θ∈positiveDomain R) (a : Index→ℝ) :
    boundedVector hR (combinedDrive_memLp hR hθ a)=boundedVector hR (rawCombination_memLp hθ a)-
      projection hR hθ (boundedVector hR (rawCombination_memLp hθ a)) := by
  change boundedVector hR (bounded_sum_memLp (drive_memLp_top hR hθ) a)=
    boundedVector hR (bounded_sum_memLp (rawDrive_memLp_top hθ) a)-
      projection hR hθ (boundedVector hR (bounded_sum_memLp (rawDrive_memLp_top hθ) a))
  rw [boundedVector_sum hR (drive_memLp_top hR hθ),
    boundedVector_sum hR (rawDrive_memLp_top hθ)]
  simp only [drive_vector,smul_sub,Finset.sum_sub_distrib,map_sum,map_smul]

theorem quadratic_zero_iff_raw_kernel {R : ℝ} (hR : 0<R) {θ : Parameter}
    (hθ : θ∈positiveDomain R) (a : Index→ℝ) :
    quadraticResponse hR hθ a=0 ↔
      boundedVector hR (rawCombination_memLp hθ a)∈(physicalDifference hR.le hθ).ker := by
  rw [quadratic_zero_iff_drive_zero,←boundedVector_zero_iff hR (combinedDrive_memLp hR hθ a),
    combined_vector]
  exact micro_residual_zero_iff_kernel hR hθ _

theorem quadratic_zero_iff_original_invariant {R : ℝ} (hR : 0<R) {θ : Parameter}
    (hθ : θ∈positiveDomain R) (a : Index→ℝ) :
    quadraticResponse hR hθ a=0 ↔ ∃b : QuadraticPointwiseClosure.Coefficients,
      rawCombination θ a=ᵐ[cubeVolume R] (fun k=>profile θ k*QuadraticPointwiseClosure.evaluate b k) := by
  rw [quadratic_zero_iff_raw_kernel]
  exact bounded_kernel_iff_coefficients hR hθ _

end
end Resonance.ActualOnsagerKernelBridge
