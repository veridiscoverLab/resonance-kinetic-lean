import Resonance.SpacetimeEntropyNorm
import Resonance.SpacetimePhaseProduction
import Resonance.OriginalRJEntropyBalance
import Resonance.RelativeEntropyBounds

/-! The whole common current of the actual positive mild solution is tied
to the original entropy equality, including its initial and terminal terms.
The displayed measurability/bounds construct its genuine L² representative;
they do not assert a norm limit or substitute an entropy evolution law. -/
open Set MeasureTheory MeasureTheory.Measure
open scoped ENNReal
namespace Resonance.SpacetimeEntropyBalance
noncomputable section
open ResonantMeasure Thermodynamics ThermodynamicChart SpacetimePairing
open SpacetimeContinuousFields SpacetimeActualMobility SpacetimeReciprocalIdentity
open SpacetimeActualMatching SpacetimeEntropyNorm SpacetimePhaseProduction
open FreeTransport JetCollision ActualMatchedMoments ActualCoframeWeight
open PhaseRelativeEntropy PhaseCollisionEntropy MicroscopicEntropyWork

theorem original_time_norm {R T : ℝ} (hR : 0 < R) (hT : 0 ≤ T) (c : ℝ)
    {K : Set Parameter} (hK : IsCompact K) (hpos : K ⊆ positiveDomain R)
    {θ θc : Base → Parameter} (hm : Measurable θ)
    (hθ : ∀ᵐ a ∂baseMeasure T, θ a ∈ K)
    (f : ℝ → Distribution R) (hFm : Measurable (cubeFamily f))
    (hYm : Measurable (reciprocalFamily c (cubeFamily f) θ θc)) {CY Cb : ℝ}
    (hY : ∀ᵐ a ∂baseMeasure T, ‖reciprocalFamily c (cubeFamily f) θ θc a‖ ≤ CY)
    (hb : ∀ᵐ z ∂sourceMeasure R T, |sourceRatio (cubeFamily f) θ z| ≤ Cb)
    (hc : ContinuousOn f (Icc 0 T))
    (hp : ∀ t ∈ Icc 0 T, ∀ z, 0 < f t z)
    (hθc : ∀ᵐ a ∂baseMeasure T, θc a ∈ positiveDomain R) :
    ‖actualCurrent hR T c hK hpos hm hθ hFm hYm hY hb‖ ^ 2 =
      c ^ 2 * (∫ t in (0 : ℝ)..T, phaseProduction R (f t)) := by
  have hf : ∀ᵐ a ∂baseMeasure T, ∀ k, 0 < cubeFamily f a k := by
    apply (quasiMeasurePreserving_fst.ae (ae_restrict_mem measurableSet_Icc)).mono
    intro a ha k
    exact hp a.1 ha (a.2,k)
  have he := original_entropy_norm hR T c hK hpos hm hθ hFm hYm hY hb hf hθc
  rw [original_time_space_production hR.le hT f hFm hc hp,
    ←ENNReal.ofReal_mul (sq_nonneg c)] at he
  have hi : 0 ≤ ∫ t in (0 : ℝ)..T, phaseProduction R (f t) := by
    apply intervalIntegral.integral_nonneg_of_ae_restrict hT
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    exact phaseProduction_nonnegative (f t) (hp t ht)
  have h := congrArg ENNReal.toReal he
  rwa [ENNReal.toReal_ofReal (sq_nonneg _),
    ENNReal.toReal_ofReal (mul_nonneg (sq_nonneg c) hi)] at h

theorem original_mild_current_entropy {R T : ℝ} (hR : 0 < R) (hT : 0 ≤ T)
    (c : ℝ) (p₀ : JetCollision.Space R) (p : ℝ → JetCollision.Space R)
    (hp : ContinuousOn p (Icc 0 T))
    (he : ∀ t ∈ Icc 0 T, readback (p t) = transport R t (readback p₀) +
      ∫ s in (0 : ℝ)..t, c • transport R (t-s)
        (SpatialCollision.collision R hR.le (readback (p s))))
    (hpositive : ∀ t ∈ Icc 0 T, ∀ z, 0 < readback (p t) z)
    (hi : ∀ t ∈ Icc 0 T, ∀ X, actualMoments R (readback (p t)) X ∈ momentImage R)
    (θ₀ : SpatialTorus → Parameter) (hθ₀ : ∀ X, θ₀ X ∈ positiveDomain R)
    (hinit : ∀ z, readback p₀ z = WeightedJointMeasure.profile (θ₀ z.1) z.2)
    {K : Set Parameter} (hK : IsCompact K) (hpos : K ⊆ positiveDomain R)
    {θ : Base → Parameter} (hm : Measurable θ)
    (hθ : ∀ᵐ a ∂baseMeasure T, θ a ∈ K)
    (hFm : Measurable (cubeFamily (fun t => readback (p t))))
    (hYm : Measurable (reciprocalFamily c (cubeFamily (fun t => readback (p t))) θ
      (matchedFamily hR (fun t => readback (p t))))) {CY Cb : ℝ}
    (hY : ∀ᵐ a ∂baseMeasure T, ‖reciprocalFamily c (cubeFamily (fun t => readback (p t))) θ
      (matchedFamily hR (fun t => readback (p t))) a‖ ≤ CY)
    (hb : ∀ᵐ z ∂sourceMeasure R T,
      |sourceRatio (cubeFamily (fun t => readback (p t))) θ z| ≤ Cb) :
    ‖actualCurrent hR T c hK hpos hm hθ hFm hYm hY hb‖ ^ 2 +
      c * relativeEntropy R (readback (p T))
        (readback (coframeJet R hR (Icc 0 T) p hi T)) =
      c * (∫ t in (0 : ℝ)..T, entropyWork R (p t) (coframeJet R hR (Icc 0 T) p hi t)) := by
  have hθc : ∀ᵐ a ∂baseMeasure T,
      matchedFamily hR (fun t => readback (p t)) a ∈ positiveDomain R := by
    apply (quasiMeasurePreserving_fst.ae (ae_restrict_mem measurableSet_Icc)).mono
    intro a ha
    exact matched_positive R hR _ _ (hi a.1 ha a.2)
  rw [original_time_norm hR hT c hK hpos hm hθ _ hFm hYm hY hb
    ((readback_continuous R).comp_continuousOn hp) hpositive hθc]
  have h := OriginalRJEntropyBalance.original_RJ_microscopic_entropy_balance
    hR hT c p₀ p hp he hpositive hi θ₀ hθ₀ hinit
  nlinarith [congrArg (fun x : ℝ => c*x) h]

end
end Resonance.SpacetimeEntropyBalance
