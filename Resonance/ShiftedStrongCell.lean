import Resonance.ShiftedParameterContinuity

/-! The shifted augmented solution is an original micro resolvent for
precisely the original five-moment-compatible sources. -/
open MeasureTheory Set
open scoped ENNReal BigOperators
namespace Resonance.ShiftedStrongCell
noncomputable section
set_option maxHeartbeats 1800000
open ResonantMeasure WeightedJointMeasure Thermodynamics ReferenceFrequencySpace CollisionFrequency
open ActualPairNormalization PhysicalFiveBasis PhysicalMomentProjection PhysicalProjectionKernel
open PhysicalFrequencyCoordinates PhysicalWeightedCoercivity ReferenceMomentFunctionals
open LinftyPhysicalDomain LinftyPhysicalForm LinftyFiveAugmentation
open PositiveLossShift ShiftedAugmentation ShiftedParameterContinuity
open StrongBoundedCell (sourceVector source_memLp_reference)

theorem synthesisTop_eq_synthesis_ae {R : ℝ} (hR : 0<R) {θ : Parameter}
    (hθ : θ∈positiveDomain R) (b : Parameter) :
    synthesisTop hθ b=ᵐ[cubeVolume R] synthesis hR.le hθ b := by
  filter_upwards [synthesisTop_ae hθ b,
    (reference_volume_equivalent hR).1.ae_eq (synthesis_ae hR.le hθ b)] with k ht hs
  rw [ht,hs]
  simp only [Entropy.denominator,Finset.mul_sum,basisFunction]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem gap_ae {R : ℝ} (hR : 0<R) {θ : Parameter}
    (hθ : θ∈positiveDomain R) {z : ℝ} (hz : 0≤z) (f : Lp ℝ ∞ (cubeVolume R)) :
    (f-multiplier hR hθ hz f)=ᵐ[cubeVolume R]
      (fun k=>z*shiftedDivide hR hθ hz f k) := by
  filter_upwards [Lp.coeFn_sub f (multiplier hR hθ hz f),multiplier_ae hR hθ hz f,
    shiftedDivide_ae hR hθ hz f,loss_positive_ae hR hθ] with k hs hm hu hn
  simp only [Pi.sub_apply] at hs
  rw [hs,hm,hu,fraction]
  have hd := (add_pos_of_pos_of_nonneg hn hz).ne'
  field_simp
  ring

theorem kernel_gap_pairing {R : ℝ} (hR : 0<R) {θ : Parameter}
    (hθ : θ∈positiveDomain R) {z : ℝ} (hz : 0≤z)
    (f : Lp ℝ ∞ (cubeVolume R)) (b : Parameter) :
    (∫k,synthesis hR.le hθ b k*(f-multiplier hR hθ hz f) k∂cubeVolume R)=
      z*∑i : Fin 5,b i*(analysisMap hR hθ (shiftedDivide hR hθ hz f)) i := by
  calc
    _ = ∫k,z*(shiftedDivide hR hθ hz f k*(synthesisTop hθ b) k)∂cubeVolume R := by
      apply integral_congr_ae
      filter_upwards [gap_ae hR hθ hz f,synthesisTop_eq_synthesis_ae hR hθ b] with k hg hb
      rw [hg,hb]
      ring
    _ = _ := by rw [integral_const_mul,synthesisTop_pairing]

def shiftedCell {R : ℝ} (hR : 0<R) {θ : Parameter} (hθ : θ∈positiveDomain R)
    {z : ℝ} (hz : 0≤z) : Lp ℝ ∞ (cubeVolume R)→L[ℝ]Space R :=
  (shiftedDivide hR hθ hz).comp (shiftedCoordinate hR hθ hz)

theorem shifted_augmented_coordinate {R : ℝ} (hR : 0<R) {θ : Parameter}
    (hθ : θ∈positiveDomain R) {z : ℝ} (hz : 0≤z) (F : Lp ℝ ∞ (cubeVolume R)) :
    shiftedAugmented hR hθ hz (shiftedCoordinate hR hθ hz F)=F :=
  (shiftedEquiv hR hθ hz).apply_symm_apply F

theorem shifted_cell_micro {R : ℝ} (hR : 0<R) {θ : Parameter}
    (hθ : θ∈positiveDomain R) {z : ℝ} (hz : 0≤z) (F : Lp ℝ ∞ (cubeVolume R))
    (hQ : projection hR hθ (sourceVector hR F)=0) :
    projection hR hθ (shiftedCell hR hθ hz F)=0 := by
  let u := shiftedCell hR hθ hz F
  let a := analysisMap hR hθ u
  let v := synthesis hR.le hθ a
  have hp : physicalDifference hR.le hθ v=0 := by
    have hv : v∈(synthesis hR.le hθ).range := ⟨a,rfl⟩
    rw [←physical_kernel_eq_synthesis_range hR hθ] at hv
    exact hv
  have hsource := BoundedCellSource.micro_source_annihilates_kernel hR hθ
    (source_memLp_reference hR F) hQ v hp
  rw [moment_apply] at hsource
  have he := shifted_pairing hR hθ hz (shiftedCoordinate hR hθ hz F) v
  rw [shifted_augmented_coordinate,hsource,kernel_gap_pairing] at he
  have hform : physicalForm hR.le hθ u v=0 := by
    unfold physicalForm
    rw [hp,inner_zero_right]
  change 0=physicalForm hR.le hθ u v+
    (∑i : Fin 5,a i*(analysisMap hR hθ (synthesis hR.le hθ a)) i)+z*(∑i : Fin 5,a i*a i) at he
  rw [hform,zero_add,analysis_synthesis] at he
  have ha : a=0 := by
    by_contra ha
    have hpos := (gramMatrix_posDef R hR θ hθ).dotProduct_mulVec_pos ha
    simp only [star_trivial,dotProduct] at hpos
    have hs : 0≤∑i : Fin 5,a i*a i := Finset.sum_nonneg (fun i _=>mul_self_nonneg (a i))
    nlinarith
  change synthesis hR.le hθ (gramInverse hR hθ a)=0
  rw [ha,map_zero,map_zero]

theorem shifted_coordinate_equation {R : ℝ} (hR : 0<R) {θ : Parameter}
    (hθ : θ∈positiveDomain R) {z : ℝ} (hz : 0≤z) (F : Lp ℝ ∞ (cubeVolume R))
    (hQ : projection hR hθ (sourceVector hR F)=0) :
    shiftedCoordinate hR hθ hz F+AmbientLinftyCompact.operator hR hθ
      (multiplier hR hθ hz (shiftedCoordinate hR hθ hz F))=F := by
  have ha : analysisMap hR hθ (shiftedCell hR hθ hz F)=0 := by
    rw [←projection_moments,shifted_cell_micro hR hθ hz F hQ,map_zero]
  have hc : correction hR hθ (multiplier hR hθ hz (shiftedCoordinate hR hθ hz F))=0 := by
    change synthesisTop hθ (analysisMap hR hθ (shiftedCell hR hθ hz F))=0
    rw [ha,map_zero]
  have he := shifted_augmented_coordinate hR hθ hz F
  change shiftedCoordinate hR hθ hz F+
    (AmbientLinftyCompact.operator hR hθ (multiplier hR hθ hz (shiftedCoordinate hR hθ hz F))+
      correction hR hθ (multiplier hR hθ hz (shiftedCoordinate hR hθ hz F)))=F at he
  simpa only [hc,add_zero] using he

theorem actual_shifted_cell_pairing {R : ℝ} (hR : 0<R) {θ : Parameter}
    (hθ : θ∈positiveDomain R) {z : ℝ} (hz : 0≤z) (F : Lp ℝ ∞ (cubeVolume R))
    (hQ : projection hR hθ (sourceVector hR F)=0) (v : Space R) :
    physicalForm hR.le hθ (shiftedCell hR hθ hz F) v+
      (∫k,v k*(shiftedCoordinate hR hθ hz F-
        multiplier hR hθ hz (shiftedCoordinate hR hθ hz F)) k∂cubeVolume R)=
          ∫k,v k*F k∂cubeVolume R := by
  have ha : analysisMap hR hθ (shiftedCell hR hθ hz F)=0 := by
    rw [←projection_moments,shifted_cell_micro hR hθ hz F hQ,map_zero]
  have he := shifted_pairing hR hθ hz (shiftedCoordinate hR hθ hz F) v
  rw [shifted_augmented_coordinate] at he
  change _=physicalForm hR.le hθ (shiftedCell hR hθ hz F) v+
    (∑i : Fin 5,(analysisMap hR hθ (shiftedCell hR hθ hz F)) i*(analysisMap hR hθ v) i)+_ at he
  simpa only [ha,Pi.zero_apply,zero_mul,Finset.sum_const_zero,add_zero] using he.symm

end
end Resonance.ShiftedStrongCell
