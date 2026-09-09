import Resonance.NormalizedLossSmooth

/-! The actual inverse-loss map from bounded forcing into the complete
physical weighted space is smooth in all five RJ parameters. The fixed
reference division is constructed from an already proved actual cell
coordinate, not assumed bounded. -/
open MeasureTheory Set
open scoped ENNReal Topology ContDiff
namespace Resonance.PhysicalDivideSmooth
noncomputable section
set_option maxHeartbeats 1400000
open ResonantMeasure Thermodynamics WeightedJointMeasure CollisionFrequency
open ActualPairNormalization ReferenceFrequencySpace JointWeightComparison
open LinftyMultiplication NormalizedLossSmooth

def referenceDivide {R : ℝ} (hR : 0<R) : X R→L[ℝ]Space R :=
  (LinftyPhysicalDomain.divide hR (unitParameter_positive R)).comp
    (operatorMap R (lossRatioMap hR.le unitParameter))

theorem referenceDivide_ae {R : ℝ} (hR : 0<R) (f : X R) :
    referenceDivide hR f=ᵐ[cubeVolume R] fun k=>f k/referenceFrequency R k := by
  filter_upwards [LinftyPhysicalDomain.divide_ae_volume hR (unitParameter_positive R)
      (operatorMap R (lossRatioMap hR.le unitParameter) f),
    operatorMap_apply_ae R (lossRatioMap hR.le unitParameter) f,
    lossRatioMap_ae hR.le (unitParameter_positive R),
    LinftyPhysicalDomain.loss_positive_ae hR (unitParameter_positive R)] with k hd hm hl hn
  change referenceDivide hR f k=_ at hd
  rw [hd,hm,hl]
  field_simp

def divideMap {R : ℝ} (hR : 0<R) (θ : Parameter) : X R→L[ℝ]Space R :=
  (referenceDivide hR).comp (inverseOperator hR.le θ)

theorem divideMap_ae {R : ℝ} (hR : 0<R) {θ : Parameter} (hθ : θ∈positiveDomain R)
    (f : X R) :
    divideMap hR θ f=ᵐ[cubeVolume R] fun k=>f k/lossFrequency R (profile θ) k := by
  filter_upwards [referenceDivide_ae hR (inverseOperator hR.le θ f),
    inverseOperator_ae hR hθ f,CornerInverseFrequency.referenceFrequency_positive_ae hR]
    with k hd hi hr
  change divideMap hR θ f k=_ at hd
  rw [hd,hi]
  field_simp

theorem divideMap_eq {R : ℝ} (hR : 0<R) {θ : Parameter} (hθ : θ∈positiveDomain R) :
    divideMap hR θ=LinftyPhysicalDomain.divide hR hθ := by
  apply ContinuousLinearMap.ext
  intro f
  apply Lp.ext
  exact (reference_volume_equivalent hR).2.ae_eq
    ((divideMap_ae hR hθ f).trans (LinftyPhysicalDomain.divide_ae_volume hR hθ f).symm)

theorem divideMap_contDiffAt {R : ℝ} (hR : 0<R) {θ : Parameter}
    (hθ : θ∈positiveDomain R) : ContDiffAt ℝ ∞ (divideMap hR) θ :=
  contDiffAt_const.clm_comp (inverseOperator_contDiffAt hR hθ)

theorem actual_divideMap_contDiffOn {R : ℝ} (hR : 0<R) :
    ContDiffOn ℝ ∞ (divideMap hR) (positiveDomain R) :=
  fun _ hθ=>(divideMap_contDiffAt hR hθ).contDiffWithinAt

end
end Resonance.PhysicalDivideSmooth
