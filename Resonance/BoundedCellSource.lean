import Resonance.PhysicalVariationalCell

/-! Actual bounded measurable drives, their unweighted pairing on H_nu,
and the original five-moment compatibility condition. -/
open MeasureTheory Set
open scoped ENNReal BigOperators
namespace Resonance.BoundedCellSource
noncomputable section
set_option maxHeartbeats 800000
open ResonantMeasure WeightedJointMeasure Thermodynamics ReferenceFrequencySpace
open ActualPairNormalization (cubeVolume)
open ReferenceMomentFunctionals PhysicalFiveBasis PhysicalMomentProjection PhysicalProjectionKernel
open PhysicalFrequencyCoordinates PhysicalWeightedCoercivity PhysicalVariationalCell

theorem bounded_memLp_two {R : ℝ} (hR : 0<R) {F : E→ℝ}
    (hF : MemLp F ∞ (referenceMeasure R)) : MemLp F 2 (referenceMeasure R) := by
  letI := reference_finite hR.le
  exact hF.mono_exponent le_top

def boundedVector {R : ℝ} (hR : 0<R) {F : E→ℝ}
    (hF : MemLp F ∞ (referenceMeasure R)) : Space R := (bounded_memLp_two hR hF).toLp F

theorem boundedVector_ae {R : ℝ} (hR : 0<R) {F : E→ℝ}
    (hF : MemLp F ∞ (referenceMeasure R)) :
    (boundedVector hR hF : E→ℝ)=ᵐ[cubeVolume R]F :=
  (reference_volume_equivalent hR).1.ae_eq (bounded_memLp_two hR hF).coeFn_toLp

theorem moment_basis {R : ℝ} (hR : 0<R) {θ : Parameter} (hθ : θ∈positiveDomain R)
    {F : E→ℝ} (hF : MemLp F ∞ (referenceMeasure R)) (i : Fin 5) :
    moment hR hF (basisVector hR.le hθ i)=analysisMap hR hθ (boundedVector hR hF) i := by
  rw [moment_apply,analysisMap_apply]
  apply integral_congr_ae
  filter_upwards [(reference_volume_equivalent hR).1.ae_eq (basisVector_ae hR.le hθ i),
    boundedVector_ae hR hF] with k hk hFk
  rw [hk,hFk,mul_comm]

theorem micro_source_annihilates_kernel {R : ℝ} (hR : 0<R) {θ : Parameter}
    (hθ : θ∈positiveDomain R) {F : E→ℝ} (hF : MemLp F ∞ (referenceMeasure R))
    (hQ : projection hR hθ (boundedVector hR hF)=0) :
    ∀v∈(physicalDifference hR.le hθ).ker,moment hR hF v=0 := by
  have ha : analysisMap hR hθ (boundedVector hR hF)=0 := by
    rw [←projection_moments,hQ,map_zero]
  intro v hv
  have hr : v∈(synthesis hR.le hθ).range := by
    rw [←projection_range hR hθ,projection_range_eq_kernel hR hθ]
    exact hv
  obtain ⟨b,rfl⟩ := hr
  change moment hR hF (synthesis hR.le hθ b)=0
  rw [synthesis_apply,map_sum]
  simp only [map_smul,moment_basis,ha,Pi.zero_apply,smul_zero,Finset.sum_const_zero]

def cell {R : ℝ} (hR : 0<R) {θ : Parameter} (hθ : θ∈positiveDomain R)
    {F : E→ℝ} (hF : MemLp F ∞ (referenceMeasure R)) : Micro hR hθ :=
  solve hR hθ (moment hR hF)

theorem actual_bounded_cell_pairing {R : ℝ} (hR : 0<R) {θ : Parameter}
    (hθ : θ∈positiveDomain R) {F : E→ℝ} (hF : MemLp F ∞ (referenceMeasure R))
    (hQ : projection hR hθ (boundedVector hR hF)=0) (v : Space R) :
    physicalForm hR.le hθ (cell hR hθ hF) v=∫k,v k*F k∂cubeVolume R := by
  exact (solve_full_pairing hR hθ _ (micro_source_annihilates_kernel hR hθ hF hQ) v).trans
    (moment_apply hR hF v)

theorem actual_bounded_cell_unique {R : ℝ} (hR : 0<R) {θ : Parameter}
    (hθ : θ∈positiveDomain R) {F : E→ℝ} (hF : MemLp F ∞ (referenceMeasure R))
    {u : Micro hR hθ}
    (hu : ∀v : Space R,physicalForm hR.le hθ u v=∫k,v k*F k∂cubeVolume R) :
    u=cell hR hθ hF := by
  apply solve_unique
  intro v
  rw [hu,moment_apply]

theorem source_norm_bound {R : ℝ} (hR : 0<R) {F : E→ℝ}
    (hF : MemLp F ∞ (referenceMeasure R)) {M : ℝ} (hM : 0≤M)
    (hb : ∀ᵐk∂referenceMeasure R,‖F k‖≤M) :
    ‖moment hR hF‖≤‖inverseVector hR‖*M := by
  apply (moment hR hF).opNorm_le_bound (mul_nonneg (norm_nonneg _) hM)
  intro v
  change ‖inner ℝ (inverseVector hR) (LpOperators.multiplyCLM hF v)‖≤_
  calc
    _ ≤ ‖inverseVector hR‖*‖LpOperators.multiplyCLM hF v‖ := norm_inner_le_norm _ _
    _ ≤ ‖inverseVector hR‖*(M*‖v‖) :=
      mul_le_mul_of_nonneg_left (PhysicalFrequencyBounds.multiply_explicit_bound hF hb v)
        (norm_nonneg _)
    _ = _ := (mul_assoc _ _ _).symm

end
end Resonance.BoundedCellSource
