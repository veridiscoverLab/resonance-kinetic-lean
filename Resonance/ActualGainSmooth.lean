import Resonance.ActualPairWeightSmooth

/-! Full fixed-space C-infinity dependence of the actual signed gain
J_theta, including both N normalizations and the vanishing input loss.
The resulting map is proved equal to the original compact operator. -/
open MeasureTheory Set
open scoped ENNReal ContDiff
namespace Resonance.ActualGainSmooth
noncomputable section
set_option maxHeartbeats 1800000
open ResonantMeasure Thermodynamics WeightedJointMeasure CollisionFrequency
open ActualPairNormalization ProfileBanachSmooth LinftyMultiplication
open NormalizedLossSmooth ActualPairWeightSmooth

def denominatorFamily (R : ℝ) (θ : Parameter) : X R→L[ℝ]X R :=
  operatorMap R (CubeLinftyCoordinates.embed R (denominatorMap R θ))

theorem denominatorFamily_contDiff (R : ℝ) : ContDiff ℝ ∞ (denominatorFamily R) :=
  (operatorMap R).contDiff.comp ((CubeLinftyCoordinates.embed R).contDiff.comp (denominatorMap R).contDiff)

theorem denominatorFamily_ae (R : ℝ) (θ : Parameter) (f : X R) :
    denominatorFamily R θ f=ᵐ[cubeVolume R] fun k=>f k*(profile θ k)⁻¹ := by
  filter_upwards [operatorMap_apply_ae R (CubeLinftyCoordinates.embed R (denominatorMap R θ)) f,
    CubeLinftyCoordinates.embed_ae R (denominatorMap R θ),ae_restrict_mem (measurable_cube R)]
    with k ho he hk
  change denominatorFamily R θ f k=_ at ho
  rw [ho,he,CubeLinftyCoordinates.zeroExtension_apply R _ ⟨k,hk⟩,denominatorMap_apply,
    profile_eq_inverse_denominator,inv_inv]

def inputFamily {R : ℝ} (hR : 0<R) (θ : Parameter) : X R→L[ℝ]X R :=
  (denominatorFamily R θ).comp (inverseOperator hR.le θ)

theorem inputFamily_contDiffAt {R : ℝ} (hR : 0<R) {θ : Parameter} (hθ : θ∈positiveDomain R) :
    ContDiffAt ℝ ∞ (inputFamily hR) θ :=
  (denominatorFamily_contDiff R).contDiffAt.clm_comp (inverseOperator_contDiffAt hR hθ)

theorem inputFamily_ae {R : ℝ} (hR : 0<R) {θ : Parameter} (hθ : θ∈positiveDomain R) (f : X R) :
    inputFamily hR θ f=ᵐ[cubeVolume R] fun k=>
      (f k*(referenceFrequency R k/lossFrequency R (profile θ) k))*(profile θ k)⁻¹ := by
  filter_upwards [denominatorFamily_ae R θ (inverseOperator hR.le θ f),
    inverseOperator_ae hR hθ f] with k hd hi
  change inputFamily hR θ f k=_ at hd
  rw [hd,hi]

def gainFamily {R : ℝ} (hR : 0<R) (θ : Parameter) : X R→L[ℝ]X R :=
  (denominatorFamily R θ).comp ((pairFamily hR θ).comp (inputFamily hR θ))

theorem gainFamily_contDiffAt {R : ℝ} (hR : 0<R) {θ : Parameter} (hθ : θ∈positiveDomain R) :
    ContDiffAt ℝ ∞ (gainFamily hR) θ :=
  (denominatorFamily_contDiff R).contDiffAt.clm_comp
    ((pairFamily_contDiffAt hR hθ).clm_comp (inputFamily_contDiffAt hR hθ))

theorem gainFamily_ae {R : ℝ} (hR : 0<R) {θ : Parameter} (hθ : θ∈positiveDomain R) (f : X R) :
    gainFamily hR θ f=ᵐ[cubeVolume R]
      fun k=>∫p,AmbientLinftyCompact.kernel R θ k p*f p∂cubeVolume R := by
  let g := inputFamily hR θ f
  filter_upwards [denominatorFamily_ae R θ (pairFamily hR θ g),pairFamily_ae hR hθ g,
    ae_restrict_mem (measurable_cube R)] with k hd hp hk
  change gainFamily hR θ f k=_ at hd
  rw [hd,hp,mul_comm,←integral_const_mul]
  apply integral_congr_ae
  filter_upwards [inputFamily_ae hR hθ f,CornerInverseFrequency.referenceFrequency_positive_ae hR,
    LinftyPhysicalDomain.loss_positive_ae hR hθ,ae_restrict_mem (measurable_cube R)]
    with p hi hr hn hpc
  change (profile θ k)⁻¹*((referenceFrequency R p)⁻¹*
      ((IncomingPairDensity.density R (weight θ) (k,p)).toReal-
        2*(CrossPairDensity.density R (weight θ) (k,p)).toReal)*g p)=_
  change g p=_ at hi
  rw [hi]
  unfold AmbientLinftyCompact.kernel
  field_simp [hr.ne',(profile_pos hθ hk).ne',(profile_pos hθ hpc).ne',hn.ne']

theorem gainFamily_eq {R : ℝ} (hR : 0<R) {θ : Parameter} (hθ : θ∈positiveDomain R) :
    gainFamily hR θ=AmbientLinftyCompact.operator hR hθ := by
  apply ContinuousLinearMap.ext
  intro f
  apply Lp.ext
  exact (gainFamily_ae hR hθ f).trans (AmbientLinftyCompact.operator_ae hR hθ f).symm

theorem actual_gainFamily_contDiffOn {R : ℝ} (hR : 0<R) :
    ContDiffOn ℝ ∞ (gainFamily hR) (positiveDomain R) :=
  fun _ hθ=>(gainFamily_contDiffAt hR hθ).contDiffWithinAt

end
end Resonance.ActualGainSmooth
