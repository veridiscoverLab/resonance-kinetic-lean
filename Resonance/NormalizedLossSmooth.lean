import Resonance.LinftyMultiplication

/-! Actual C-infinity parameter dependence of nu_theta/nu_* and its
reciprocal multiplier. These live in L-infinity; no continuous extension
of the corner ratio is imposed. -/
open MeasureTheory Set
open scoped ENNReal Topology ContDiff
namespace Resonance.NormalizedLossSmooth
noncomputable section
set_option maxHeartbeats 1600000
open ResonantMeasure Thermodynamics WeightedJointMeasure CollisionFrequency
open ActualPairNormalization CollisionMultilinear ProfileBanachSmooth
open LinftyMultiplication

def lossRatioMap {R : ℝ} (hR : 0≤R) (θ : Parameter) : X R :=
  operatorMap R (CubeLinftyCoordinates.embed R (denominatorMap R θ))
    (NormalizedFiberMultilinear.continuous hR ![1,2,3] (fun _=>profileMap R θ))

theorem lossRatioMap_ae {R : ℝ} (hR : 0≤R) {θ : Parameter}
    (hθ : θ∈positiveDomain R) :
    lossRatioMap hR θ=ᵐ[cubeVolume R] fun k=>lossFrequency R (profile θ) k/referenceFrequency R k := by
  have hparent (k : E) :
      (∫q,pointParent R ![1,2,3] q (fun _=>profileMap R θ)∂CollisionFiber.fiberMeasure R k)=
      ∫q,profile θ (q 1)*profile θ (q 2)*profile θ (q 3)∂CollisionFiber.fiberMeasure R k := by
    apply integral_congr_ae
    filter_upwards [CollisionFiber.fiber_support R k] with q hq
    simp only [pointParent_apply,Fin.prod_univ_succ,Fin.prod_univ_zero,mul_one,
      Matrix.cons_val_zero,Matrix.cons_val_succ]
    rw [zeroEval_inside R _ (hq.1 1),zeroEval_inside R _ (hq.1 2),zeroEval_inside R _ (hq.1 3),
      profileMap_apply hθ,profileMap_apply hθ,profileMap_apply hθ]
    ring
  filter_upwards [operatorMap_apply_ae R (CubeLinftyCoordinates.embed R (denominatorMap R θ))
      (NormalizedFiberMultilinear.continuous hR ![1,2,3] (fun _=>profileMap R θ)),
    CubeLinftyCoordinates.embed_ae R (denominatorMap R θ),
    NormalizedFiberMultilinear.continuous_apply_ae hR ![1,2,3] (fun _=>profileMap R θ),
    ae_restrict_mem (measurable_cube R)] with k he hden hp hk
  change lossRatioMap hR θ k=_ at he
  rw [he,hden,hp,CubeLinftyCoordinates.zeroExtension_apply R _ ⟨k,hk⟩,
    denominatorMap_apply,hparent]
  unfold lossFrequency FiberContinuity.fiberReadout
  rw [profile_eq_inverse_denominator,inv_inv]
  ring

theorem lossRatioMap_contDiffAt {R : ℝ} (hR : 0≤R) {θ : Parameter}
    (hθ : θ∈positiveDomain R) : ContDiffAt ℝ ∞ (lossRatioMap hR) θ := by
  have hden := ((CubeLinftyCoordinates.embed R).contDiff (n:=∞)).comp (denominatorMap R).contDiff
  have hp : ContDiffAt ℝ ∞ (fun β : Parameter=>(fun _ : Fin 3=>profileMap R β)) θ :=
    contDiffAt_pi.mpr (fun _=>profileMap_contDiffAt hθ)
  exact ((operatorMap R).contDiff.contDiffAt.comp θ hden.contDiffAt).clm_apply
    ((NormalizedFiberMultilinear.continuous hR ![1,2,3]).contDiff.contDiffAt.comp θ hp)

theorem actual_lossRatioMap_contDiffOn {R : ℝ} (hR : 0≤R) :
    ContDiffOn ℝ ∞ (lossRatioMap hR) (positiveDomain R) :=
  fun _ hθ=>(lossRatioMap_contDiffAt hR hθ).contDiffWithinAt

def inverseVector {R : ℝ} (hR : 0<R) {θ : Parameter} (hθ : θ∈positiveDomain R) : X R :=
  (StrongCellWeightedContinuity.ratio_memLp hR hθ).toLp _

theorem inverseVector_ae {R : ℝ} (hR : 0<R) {θ : Parameter} (hθ : θ∈positiveDomain R) :
    inverseVector hR hθ=ᵐ[cubeVolume R] fun k=>referenceFrequency R k/lossFrequency R (profile θ) k :=
  MemLp.coeFn_toLp _

theorem actual_reciprocal_product {R : ℝ} (hR : 0<R) {θ : Parameter} (hθ : θ∈positiveDomain R) :
    ∀ᵐk∂cubeVolume R,lossRatioMap hR.le θ k*inverseVector hR hθ k=1 := by
  filter_upwards [lossRatioMap_ae hR.le hθ,inverseVector_ae hR hθ,
    CornerInverseFrequency.referenceFrequency_positive_ae hR,
    LinftyPhysicalDomain.loss_positive_ae hR hθ] with k hl hi hr hn
  rw [hl,hi]
  field_simp

def inverseOperator {R : ℝ} (hR : 0≤R) (θ : Parameter) : X R→L[ℝ]X R :=
  Ring.inverse (operatorMap R (lossRatioMap hR θ))

theorem inverseOperator_eq {R : ℝ} (hR : 0<R) {θ : Parameter} (hθ : θ∈positiveDomain R) :
    inverseOperator hR.le θ=operatorMap R (inverseVector hR hθ) :=
  inverse_operatorMap R _ _ (actual_reciprocal_product hR hθ)

theorem inverseOperator_ae {R : ℝ} (hR : 0<R) {θ : Parameter}
    (hθ : θ∈positiveDomain R) (f : X R) :
    inverseOperator hR.le θ f=ᵐ[cubeVolume R]
      fun k=>f k*(referenceFrequency R k/lossFrequency R (profile θ) k) := by
  rw [inverseOperator_eq hR hθ]
  filter_upwards [operatorMap_apply_ae R (inverseVector hR hθ) f,inverseVector_ae hR hθ]
    with k ho hi
  rw [ho,hi]

theorem inverseOperator_eq_actual_multiplier {R : ℝ} (hR : 0<R) {θ : Parameter}
    (hθ : θ∈positiveDomain R) :
    inverseOperator hR.le θ=StrongCellWeightedContinuity.multiplier hR hθ := by
  ext f
  exact (inverseOperator_ae hR hθ f).trans
    (CubeLinftyMultiplier.operator_ae (StrongCellWeightedContinuity.ratio_memLp hR hθ) f).symm

theorem inverseOperator_contDiffAt {R : ℝ} (hR : 0<R) {θ : Parameter}
    (hθ : θ∈positiveDomain R) : ContDiffAt ℝ ∞ (inverseOperator hR.le) θ := by
  have hi := contDiffAt_ringInverse (𝕜:=ℝ) (n:=∞)
    (LinftyMultiplication.unit R _ _ (actual_reciprocal_product hR hθ))
  exact hi.comp θ ((operatorMap R).contDiff.contDiffAt.comp θ (lossRatioMap_contDiffAt hR.le hθ))

theorem actual_inverseOperator_contDiffOn {R : ℝ} (hR : 0<R) :
    ContDiffOn ℝ ∞ (inverseOperator hR.le) (positiveDomain R) :=
  fun _ hθ=>(inverseOperator_contDiffAt hR hθ).contDiffWithinAt

end
end Resonance.NormalizedLossSmooth
