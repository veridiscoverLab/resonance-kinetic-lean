import Resonance.ActualPairWeightLinear

/-! The original two pair densities are recovered from the actual
complete-weight linear operators. Their fixed-space parameter family is
C-infinity with all four RJ factors retained. -/
open MeasureTheory Set
open scoped ENNReal ContDiff
namespace Resonance.ActualPairWeightSmooth
noncomputable section
set_option maxHeartbeats 1800000
open ResonantMeasure Thermodynamics WeightedJointMeasure CollisionFrequency
open ActualPairNormalization QuartetWeightSpace ActualPairWeightLinear
open LinftyMultiplication

theorem raw_profile_extension {R : ℝ} {θ : Parameter} (hθ : θ∈positiveDomain R)
    {Φ : FourMomenta→ℝ} (hpos : ∀q∈CoareaNormalization.allFourFlags R,0≤Φ q)
    (he : ∀q∈CoareaNormalization.allFourFlags R,weight θ q=ENNReal.ofReal (Φ q)) (q : FourMomenta) :
    rawWeight R (profileWeightMap R θ) q=CoareaNormalization.sharpReadout R Φ q := by
  by_cases hq : q∈CoareaNormalization.allFourFlags R
  · rw [rawWeight_inside R _ hq,CoareaNormalization.sharpReadout,Set.indicator_of_mem hq,
      profileWeightMap_apply hθ]
    have hp : 0≤∏i : Fin 4,profile θ (q i) :=
      Finset.prod_nonneg (fun i _=>(profile_pos hθ (hq i)).le)
    have hh := congrArg ENNReal.toReal (he q hq)
    simpa only [weight,ENNReal.toReal_ofReal hp,ENNReal.toReal_ofReal (hpos q hq)] using hh
  · rw [rawWeight_outside R _ hq,CoareaNormalization.sharpReadout,Set.indicator_of_notMem hq]

theorem incomingKernel_profile {R : ℝ} (hR : 0≤R) {θ : Parameter}
    (hθ : θ∈positiveDomain R) (k p : E) :
    incomingKernel R (profileWeightMap R θ) k p=(referenceFrequency R p)⁻¹*
      (IncomingPairDensity.density R (weight θ) (k,p)).toReal := by
  obtain ⟨Φ,hΦ,hpos,he⟩ := CrossDensityContinuity.actual_weight_extension hθ
  rw [IncomingRowPointwise.density_congr_on_flags R _ _ he,
    IncomingRowPointwise.density_toReal_sphereRow hR Φ hΦ hpos]
  unfold incomingKernel PairWeightLinear.kernel PairWeightLinear.fiber incomingFactor
    IncomingRowPointwise.sphereRow IncomingRowPointwise.sphereIntegral
  simp_rw [raw_profile_extension hθ hpos he]
  ring

theorem crossKernel_profile {R : ℝ} (hR : 0≤R) {θ : Parameter}
    (hθ : θ∈positiveDomain R) (k p : E) :
    crossKernel R (profileWeightMap R θ) k p=(referenceFrequency R p)⁻¹*
      (CrossPairDensity.density R (weight θ) (k,p)).toReal := by
  obtain ⟨Φ,hΦ,hpos,he⟩ := CrossDensityContinuity.actual_weight_extension hθ
  rw [CrossDensityContinuity.density_congr_on_flags R _ _ he,
    CrossDensityContinuity.density_toReal_planeRow hR Φ hΦ hpos]
  unfold crossKernel PairWeightLinear.kernel PairWeightLinear.fiber crossFactor CrossRowPointwise.planeRow
  rw [CrossRowPointwise.planeIntegral_box hR]
  simp_rw [raw_profile_extension hθ hpos he]
  ring

def pairFamily {R : ℝ} (hR : 0<R) (θ : Parameter) : X R→L[ℝ]X R :=
  incomingOperator hR (profileWeightMap R θ)-(2:ℝ) • crossOperator hR (profileWeightMap R θ)

theorem pairFamily_contDiffAt {R : ℝ} (hR : 0<R) {θ : Parameter}
    (hθ : θ∈positiveDomain R) : ContDiffAt ℝ ∞ (pairFamily hR) θ :=
  ((incomingOperator hR).contDiff.contDiffAt.comp θ (profileWeightMap_contDiffAt hθ)).sub
    (((crossOperator hR).contDiff.contDiffAt.comp θ (profileWeightMap_contDiffAt hθ)).const_smul 2)

theorem actual_pairFamily_contDiffOn {R : ℝ} (hR : 0<R) :
    ContDiffOn ℝ ∞ (pairFamily hR) (positiveDomain R) :=
  fun _ hθ=>(pairFamily_contDiffAt hR hθ).contDiffWithinAt

theorem incoming_product_integrable {R : ℝ} (hR : 0<R) (W : WeightSpace R) (f : X R)
    {k : E} (hk : k∈cube R) : Integrable (fun p=>incomingKernel R W k p*f p) (cubeVolume R) :=
  PairWeightLinear.product_integrable surface R _ IncomingPairMarginal.incomingQuartet_measurable _
    (incomingFactor_measurable R) (incomingFactor_nonnegative R) (incoming_unit_integrable hR) W f hk

theorem cross_product_integrable {R : ℝ} (hR : 0<R) (W : WeightSpace R) (f : X R)
    {k : E} (hk : k∈cube R) : Integrable (fun p=>crossKernel R W k p*f p) (cubeVolume R) :=
  PairWeightLinear.product_integrable (CrossRowPointwise.finitePlaneMeasure R) R _
    CrossPairCoordinates.crossQuartet_measurable _ (crossFactor_measurable R)
    (crossFactor_nonnegative R) (cross_unit_integrable hR) W f hk

theorem pairFamily_ae {R : ℝ} (hR : 0<R) {θ : Parameter} (hθ : θ∈positiveDomain R) (f : X R) :
    pairFamily hR θ f=ᵐ[cubeVolume R] fun k=>∫p,
      ((referenceFrequency R p)⁻¹*((IncomingPairDensity.density R (weight θ) (k,p)).toReal-
        2*(CrossPairDensity.density R (weight θ) (k,p)).toReal))*f p∂cubeVolume R := by
  let W := profileWeightMap R θ
  filter_upwards [incomingOperator_ae hR W f,crossOperator_ae hR W f,
    Lp.coeFn_sub (incomingOperator hR W f) ((2:ℝ) • crossOperator hR W f),
    Lp.coeFn_smul (2:ℝ) (crossOperator hR W f),ae_restrict_mem (measurable_cube R)]
    with k hi hc hs hm hk
  simp only [Pi.sub_apply,Pi.smul_apply,smul_eq_mul] at hs hm
  change (incomingOperator hR W f-(2:ℝ) • crossOperator hR W f) k=_
  rw [hs,hm,hi,hc,←integral_const_mul,
    ←integral_sub (incoming_product_integrable hR W f hk)
      ((cross_product_integrable hR W f hk).const_mul 2)]
  apply integral_congr_ae
  apply ae_of_all
  intro p
  change incomingKernel R (profileWeightMap R θ) k p*f p-
    2*(crossKernel R (profileWeightMap R θ) k p*f p)=_
  rw [incomingKernel_profile hR.le hθ,crossKernel_profile hR.le hθ]
  ring

end
end Resonance.ActualPairWeightSmooth
