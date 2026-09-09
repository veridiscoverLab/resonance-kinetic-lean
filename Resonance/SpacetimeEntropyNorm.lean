import Resonance.SpacetimeProductionIntegral
import Resonance.SpacetimeMultiplierOperators
import Resonance.SpacetimeDifferenceSlices

/-! The actual reciprocal current norm equals c² times the original entropy
production over the entire common base. This is an identity for the original
continuous distribution, not an entropy norm limit supplied as an assumption. -/
open Set MeasureTheory MeasureTheory.Measure
open scoped ENNReal
namespace Resonance.SpacetimeEntropyNorm
noncomputable section
open ResonantMeasure Thermodynamics SpacetimePairing SpacetimeReference
open SpacetimeContinuousFields SpacetimeDifference SpacetimeDifferenceSlices
open SpacetimeRootMultiplier SpacetimeMultiplierOperators SpacetimeActualMobility
open SpacetimeReciprocalIdentity SpacetimeProductionIntegral LpOperators
variable {R : ℝ} (hR : 0<R) (T c : ℝ) {K : Set Parameter}
  (hK : IsCompact K) (hpos : K⊆positiveDomain R)
  {θ θc : Base→Parameter} (hm : Measurable θ)
  (hθ : ∀ᵐa∂baseMeasure T,θ a∈K)
  {F : Base→C(cube R,ℝ)} (hFm : Measurable F)
  (hYm : Measurable (reciprocalFamily c F θ θc)) {CY Cb : ℝ}
  (hY : ∀ᵐa∂baseMeasure T,‖reciprocalFamily c F θ θc a‖≤CY)
  (hb : ∀ᵐz∂sourceMeasure R T,|sourceRatio F θ z|≤Cb)

def actualCurrent : Lp ℝ 2 (SpacetimeRJMeasure.measure R T θ) :=
  multiplyCLM (root_memLp hR.le T θ (sourceRatio_measurable hFm hm).aestronglyMeasurable hb)
    (physicalDifference hR T hK hpos hm hθ (source hR.le T hYm hY))

theorem actualCurrent_square_ae :
    (fun p=>(actualCurrent hR T c hK hpos hm hθ hFm hYm hY hb p)^2)
      =ᵐ[SpacetimeRJMeasure.measure R T θ]
      (fun p=>(root (sourceRatio F θ) p)^2*
        (physicalRaw (θ:=θ) (field (reciprocalFamily c F θ θc)) p)^2) := by
  have hsrc:=(SpacetimeContinuousDifference.physicalDifference_source_ae hR T hK hpos hm hθ hYm hY).trans
    (SpacetimeContinuousDifference.physicalRaw_field_ae T (reciprocalFamily c F θ θc) θ).symm
  filter_upwards [multiply_ae
    (root_memLp hR.le T θ (sourceRatio_measurable hFm hm).aestronglyMeasurable hb)
    (physicalDifference hR T hK hpos hm hθ (source hR.le T hYm hY)),hsrc]
    with p hp hr
  change (multiply
    (root_memLp hR.le T θ (sourceRatio_measurable hFm hm).aestronglyMeasurable hb)
    (physicalDifference hR T hK hpos hm hθ (source hR.le T hYm hY)) p)^2=_
  rw [hp,hr]
  ring

theorem original_entropy_norm
    (hf : ∀ᵐa∂baseMeasure T,∀k,0<F a k)
    (hθc : ∀ᵐa∂baseMeasure T,θc a∈positiveDomain R) :
    ENNReal.ofReal (‖actualCurrent hR T c hK hpos hm hθ hFm hYm hY hb‖^2)=
      ENNReal.ofReal (c^2)*
        ∫⁻a,ENNReal.ofReal (ContinuousCollisionEntropy.cubeProduction R (F a))∂baseMeasure T := by
  let Y:=reciprocalFamily c F θ θc
  let G:Joint→ℝ≥0∞:=fun p=>ENNReal.ofReal ((physicalRaw (θ:=θ) (field Y) p)^2)
  let W:Joint→ℝ≥0∞:=fun p=>ENNReal.ofReal ((root (sourceRatio F θ) p)^2)
  have hG:Measurable G:=(physicalRaw_measurable hR.le T hm (field_measurable hYm)).pow_const 2 |>.ennreal_ofReal
  have hW:AEMeasurable W (SpacetimeRJMeasure.measure R T θ) :=
    (((root_measurable hR.le T (sourceRatio_measurable hFm hm).aestronglyMeasurable).mono_ac
      (SpacetimeRJMeasure.measure_absolutelyContinuous R T θ)).pow 2).aemeasurable.ennreal_ofReal
  have hθp:∀ᵐa∂baseMeasure T,θ a∈positiveDomain R:=hθ.mono (fun _ ha=>hpos ha)
  have hf0:∀ᵐa∂baseMeasure T,∀k,0≤F a k:=hf.mono (fun _ ha k=>(ha k).le)
  calc
    _=∫⁻p,W p*G p∂SpacetimeRJMeasure.measure R T θ := by
      rw [lp_square_lintegral]
      apply lintegral_congr_ae
      filter_upwards [actualCurrent_square_ae hR T c hK hpos hm hθ hFm hYm hY hb] with p hp
      rw [hp,ENNReal.ofReal_mul (sq_nonneg _)]
    _=∫⁻p,G p∂(SpacetimeRJMeasure.measure R T θ).withDensity W :=
      (lintegral_withDensity_eq_lintegral_mul₀ hW hG.aemeasurable).symm
    _=∫⁻p,G p∂actualMeasure T F := by
      rw [actual_mobility_measure hR.le T hFm hm hf0 hθp]
    _=∫⁻p,actualWeight F p*G p∂SpacetimePairing.jointMeasure R T :=
      lintegral_withDensity_eq_lintegral_mul _ (actualWeight_measurable hR.le T hFm) hG
    _=∫⁻p,ENNReal.ofReal (c^2*productionField F p)∂SpacetimePairing.jointMeasure R T :=
      lintegral_congr_ae (scaled_density_identity T c F θ θc hf hθp hθc)
    _=_ := by
      simp_rw [ENNReal.ofReal_mul (sq_nonneg c)]
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,full_production_lintegral hR.le T hFm hf]

end
end Resonance.SpacetimeEntropyNorm
