import Resonance.BoundedMomentSum

/-! Vanishing of a projected bounded drive is exactly membership of
the actual five-dimensional collision kernel, with original a.e. data. -/
open MeasureTheory Set
open scoped ENNReal BigOperators
namespace Resonance.ProjectedDriveKernel
noncomputable section
set_option maxHeartbeats 800000
open ResonantMeasure WeightedJointMeasure Thermodynamics ReferenceFrequencySpace
open ActualPairNormalization (cubeVolume)
open ReferenceMomentFunctionals PhysicalFiveBasis PhysicalMomentProjection PhysicalProjectionKernel
open PhysicalFrequencyCoordinates PhysicalWeightedCoercivity BoundedCellSource BoundedMicroProjection

theorem boundedVector_zero_iff {R : ℝ} (hR : 0<R) {F : E→ℝ}
    (hF : MemLp F ∞ (referenceMeasure R)) :
    boundedVector hR hF=0 ↔ F=ᵐ[cubeVolume R]0 := by
  constructor
  · intro hz
    have ha := boundedVector_ae hR hF
    rw [hz] at ha
    exact ha.symm.trans ((reference_volume_equivalent hR).1.ae_eq (Lp.coeFn_zero ℝ 2 (referenceMeasure R)))
  · intro hz
    apply Lp.ext
    exact (bounded_memLp_two hR hF).coeFn_toLp.trans
      (((reference_volume_equivalent hR).2.ae_eq hz).trans (Lp.coeFn_zero ℝ 2 (referenceMeasure R)).symm)

theorem micro_residual_zero_iff_kernel {R : ℝ} (hR : 0<R) {θ : Parameter}
    (hθ : θ∈positiveDomain R) (v : Space R) :
    v-projection hR hθ v=0 ↔ v∈(physicalDifference hR.le hθ).ker := by
  constructor
  · intro hz
    have he := sub_eq_zero.mp hz
    rw [he]
    exact projection_difference_zero hR hθ v
  · intro hv
    rw [projection_fixed_kernel hR hθ hv,sub_self]

theorem projected_drive_zero_iff_kernel {R : ℝ} (hR : 0<R) {θ : Parameter}
    (hθ : θ∈positiveDomain R) {F : E→ℝ} (hF : MemLp F ∞ (referenceMeasure R)) :
    projectDrive hR hθ hF=ᵐ[cubeVolume R]0 ↔
      boundedVector hR hF∈(physicalDifference hR.le hθ).ker := by
  rw [←boundedVector_zero_iff hR (projectDrive_memLp_top hR hθ hF),projectDrive_vector]
  exact micro_residual_zero_iff_kernel hR hθ _

theorem bounded_kernel_iff_coefficients {R : ℝ} (hR : 0<R) {θ : Parameter}
    (hθ : θ∈positiveDomain R) {F : E→ℝ} (hF : MemLp F ∞ (referenceMeasure R)) :
    boundedVector hR hF∈(physicalDifference hR.le hθ).ker ↔
      ∃b : QuadraticPointwiseClosure.Coefficients,F=ᵐ[cubeVolume R]
        (fun k=>profile θ k*QuadraticPointwiseClosure.evaluate b k) := by
  rw [physical_kernel_iff_exists hR hθ]
  constructor
  · rintro ⟨b,hb⟩
    exact ⟨b,(boundedVector_ae hR hF).symm.trans hb⟩
  · rintro ⟨b,hb⟩
    exact ⟨b,(boundedVector_ae hR hF).trans hb⟩

end
end Resonance.ProjectedDriveKernel
