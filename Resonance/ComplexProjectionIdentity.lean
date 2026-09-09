import Resonance.ComplexLpProjection
import Resonance.ComplexPhysicalKernel
import Resonance.UnweightedProjectionIdentity

/-! The complex physical microprojection is exactly the original unweighted
orthogonal projection, extended through the actual reference-frequency embedding. -/
namespace Resonance.ComplexProjectionIdentity
noncomputable section
open ResonantMeasure WeightedJointMeasure Thermodynamics ReferenceFrequencySpace
open ComplexLpDecomposition ComplexLpLinear ComplexLpProjection
open ComplexPhysicalForm ComplexPhysicalKernel UnweightedProjectionIdentity

def microProjection {R : ℝ} (hR : 0<R) {θ : Parameter} (hθ : θ∈positiveDomain R) :
    ComplexSpace R→L[ℂ]ComplexSpace R := complexLift (PhysicalMomentProjection.projection hR hθ)

theorem microProjection_eq {R : ℝ} (hR : 0<R) {θ : Parameter} (hθ : θ∈positiveDomain R)
    (u : ComplexSpace R) : microProjection hR hθ u=ComplexPhysicalForm.projection hR hθ u := rfl

theorem complex_original_projection {R : ℝ} (hR : 0<R) {θ : Parameter}
    (hθ : θ∈positiveDomain R) (f : MeasureTheory.Lp ℂ 2 (ActualPairNormalization.cubeVolume R)) :
    microProjection hR hθ (complexLift (embed hR.le) f)=
      complexLift (embed hR.le)
        ((complexLift (WeightedOperator.operator hR.le hθ)).ker.starProjection f) := by
  let T : VolumeSpace R→L[ℝ]VolumeSpace R := WeightedOperator.operator hR.le hθ
  change microProjection hR hθ (complexLift (embed hR.le) f)=
    complexLift (embed hR.le) ((complexLift T).ker.starProjection f)
  rw [lift_starProjection T f]
  apply parts_injective
  · change realPart _ (lift (PhysicalMomentProjection.projection hR hθ) (lift (embed hR.le) f))=
      realPart _ (lift (embed hR.le) (lift T.ker.starProjection f))
    simp only [realPart_lift]
    exact projection_is_original_unweighted hR hθ (realPart _ f)
  · change imagPart _ (lift (PhysicalMomentProjection.projection hR hθ) (lift (embed hR.le) f))=
      imagPart _ (lift (embed hR.le) (lift T.ker.starProjection f))
    simp only [imagPart_lift]
    exact projection_is_original_unweighted hR hθ (imagPart _ f)

theorem microProjection_idempotent {R : ℝ} (hR : 0<R) {θ : Parameter}
    (hθ : θ∈positiveDomain R) (u : ComplexSpace R) :
    microProjection hR hθ (microProjection hR hθ u)=microProjection hR hθ u := by
  apply parts_injective
  · change realPart _ (lift (PhysicalMomentProjection.projection hR hθ)
      (lift (PhysicalMomentProjection.projection hR hθ) u))=realPart _ (lift _ u)
    simp only [realPart_lift,PhysicalMomentProjection.projection_idempotent]
  · change imagPart _ (lift (PhysicalMomentProjection.projection hR hθ)
      (lift (PhysicalMomentProjection.projection hR hθ) u))=imagPart _ (lift _ u)
    simp only [imagPart_lift,PhysicalMomentProjection.projection_idempotent]

theorem microProjection_range_eq_kernel {R : ℝ} (hR : 0<R) {θ : Parameter}
    (hθ : θ∈positiveDomain R) :
    (microProjection hR hθ).range=(fullDifference hR.le hθ).ker := by
  ext u
  constructor
  · rintro ⟨v,rfl⟩
    apply (complexLift_zero_iff (PhysicalFrequencyCoordinates.physicalDifference hR.le hθ) _).mpr
    constructor
    · change PhysicalFrequencyCoordinates.physicalDifference hR.le hθ
        (realPart _ (lift (PhysicalMomentProjection.projection hR hθ) v))=0
      rw [realPart_lift]
      exact PhysicalProjectionKernel.projection_difference_zero hR hθ _
    · change PhysicalFrequencyCoordinates.physicalDifference hR.le hθ
        (imagPart _ (lift (PhysicalMomentProjection.projection hR hθ) v))=0
      rw [imagPart_lift]
      exact PhysicalProjectionKernel.projection_difference_zero hR hθ _
  · intro hu
    refine ⟨u,?_⟩
    obtain ⟨hr,hi⟩ := (complexLift_zero_iff (PhysicalFrequencyCoordinates.physicalDifference hR.le hθ) u).mp hu
    apply parts_injective
    · change realPart _ (lift (PhysicalMomentProjection.projection hR hθ) u)=_
      rw [realPart_lift]
      exact PhysicalProjectionKernel.projection_fixed_kernel hR hθ hr
    · change imagPart _ (lift (PhysicalMomentProjection.projection hR hθ) u)=_
      rw [imagPart_lift]
      exact PhysicalProjectionKernel.projection_fixed_kernel hR hθ hi

end
end Resonance.ComplexProjectionIdentity
