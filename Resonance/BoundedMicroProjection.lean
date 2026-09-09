import Resonance.BoundedCellSource

/-! The actual finite-moment projection preserves bounded measurable
drives. The resulting drive is in the same physical microspace. -/
open MeasureTheory Set
open scoped ENNReal BigOperators
namespace Resonance.BoundedMicroProjection
noncomputable section
set_option maxHeartbeats 800000
open ResonantMeasure WeightedJointMeasure Thermodynamics ReferenceFrequencySpace
open ActualPairNormalization (cubeVolume)
open ReferenceMomentFunctionals PhysicalFiveBasis PhysicalMomentProjection PhysicalProjectionKernel
open PhysicalFrequencyCoordinates PhysicalWeightedCoercivity PhysicalVariationalCell BoundedCellSource
open CoareaNormalization (euclideanFive euclideanFive_continuous)

theorem synthesis_memLp_top {R : ℝ} (hR : 0<R) {θ : Parameter}
    (hθ : θ∈positiveDomain R) (b : Parameter) :
    MemLp (synthesis hR.le hθ b : E→ℝ) ∞ (referenceMeasure R) := by
  have hm : Measurable (fun k=>profile θ k*Entropy.denominator euclideanFive b k) := by
    apply (profile_measurable θ).mul
    exact Finset.measurable_sum _ (fun i _=>(euclideanFive_continuous i).measurable.const_mul (b i))
  have hc : ContinuousOn (fun k=>profile θ k*Entropy.denominator euclideanFive b k) (cube R) := by
    apply (FrequencyWeightedKernel.profile_continuousOn hθ).mul
    exact (continuous_finset_sum _ (fun i _=>(euclideanFive_continuous i).const_mul (b i))).continuousOn
  exact (continuous_cube_memLp_top hm hc).ae_eq (synthesis_ae hR.le hθ b).symm

theorem projection_memLp_top {R : ℝ} (hR : 0<R) {θ : Parameter}
    (hθ : θ∈positiveDomain R) (u : Space R) :
    MemLp (projection hR hθ u : E→ℝ) ∞ (referenceMeasure R) :=
  synthesis_memLp_top hR hθ _

def projectDrive {R : ℝ} (hR : 0<R) {θ : Parameter}
    (hθ : θ∈positiveDomain R) {F : E→ℝ}
    (hF : MemLp F ∞ (referenceMeasure R)) (k : E) : ℝ :=
  F k-projection hR hθ (boundedVector hR hF) k

theorem projectDrive_memLp_top {R : ℝ} (hR : 0<R) {θ : Parameter}
    (hθ : θ∈positiveDomain R) {F : E→ℝ}
    (hF : MemLp F ∞ (referenceMeasure R)) :
    MemLp (projectDrive hR hθ hF) ∞ (referenceMeasure R) :=
  hF.sub (projection_memLp_top hR hθ (boundedVector hR hF))

theorem projectDrive_vector {R : ℝ} (hR : 0<R) {θ : Parameter}
    (hθ : θ∈positiveDomain R) {F : E→ℝ}
    (hF : MemLp F ∞ (referenceMeasure R)) :
    boundedVector hR (projectDrive_memLp_top hR hθ hF)=
      boundedVector hR hF-projection hR hθ (boundedVector hR hF) := by
  apply Lp.ext
  filter_upwards [(bounded_memLp_two hR (projectDrive_memLp_top hR hθ hF)).coeFn_toLp,
    (bounded_memLp_two hR hF).coeFn_toLp,
    Lp.coeFn_sub (boundedVector hR hF) (projection hR hθ (boundedVector hR hF))] with k hk hFk hsk
  change boundedVector hR hF k=F k at hFk
  exact hk.trans (by rw [hsk]; change F k-_=boundedVector hR hF k-_; rw [hFk])

theorem projectDrive_micro {R : ℝ} (hR : 0<R) {θ : Parameter}
    (hθ : θ∈positiveDomain R) {F : E→ℝ}
    (hF : MemLp F ∞ (referenceMeasure R)) :
    projection hR hθ (boundedVector hR (projectDrive_memLp_top hR hθ hF))=0 := by
  rw [projectDrive_vector,map_sub,projection_idempotent,sub_self]

theorem projected_source_kills_kernel {R : ℝ} (hR : 0<R) {θ : Parameter}
    (hθ : θ∈positiveDomain R) {F : E→ℝ}
    (hF : MemLp F ∞ (referenceMeasure R)) :
    ∀v∈(physicalDifference hR.le hθ).ker,
      moment hR (projectDrive_memLp_top hR hθ hF) v=0 :=
  micro_source_annihilates_kernel hR hθ _ (projectDrive_micro hR hθ hF)

end
end Resonance.BoundedMicroProjection
