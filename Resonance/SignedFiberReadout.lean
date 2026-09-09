import Resonance.CrossSignedDisintegration
import Resonance.CollisionMultilinear

/-! Signed disintegrations are identified with the original fixed-output
fiber, using all measurable output tests and genuine integrability. -/
open MeasureTheory Set Metric
open scoped ENNReal
namespace Resonance.SignedFiberReadout
noncomputable section
set_option maxHeartbeats 1800000
open ResonantMeasure CollisionFiber

def fiberOutput (R : ℝ) (Φ : FourMomenta→ℝ) (k : E) : ℝ :=
  ∫q,Φ q∂fiberMeasure R k

theorem fiberOutput_measurable (R : ℝ) {Φ : FourMomenta→ℝ} (hΦ : Measurable Φ) :
    Measurable (fiberOutput R Φ) :=
  (hΦ.stronglyMeasurable.integral_kernel (κ:=collisionKernel R)).measurable

theorem fiberOutput_integrable {R B : ℝ} (hR : 0≤R) (hB : 0≤B)
    (Φ : FourMomenta→ℝ) (hΦ : Measurable Φ)
    (hb : ∀q∈CoareaNormalization.allFourFlags R,‖Φ q‖≤B) :
    Integrable (fiberOutput R Φ) := by
  let C := B*(fiberMassBound R).toReal
  have hi : Integrable ((cube R).indicator (fun _ : E=>C)) :=
    (integrable_indicator_iff (measurable_cube R)).mpr
      (integrableOn_const (FiberContinuity.cube_isCompact R).measure_ne_top)
  apply hi.mono' (fiberOutput_measurable R hΦ).aestronglyMeasurable
  apply ae_of_all
  intro k
  by_cases hk : k∈cube R
  · rw [Set.indicator_of_mem hk]
    letI := collisionKernel_finite hR
    haveI : IsFiniteMeasure (fiberMeasure R k) :=
      inferInstanceAs (IsFiniteMeasure (collisionKernel R k))
    apply (norm_integral_le_of_norm_le_const (C:=B) ?_).trans
    · exact mul_le_mul_of_nonneg_left
        (ENNReal.toReal_mono (fiberMassBound_lt_top R).ne (fiberMeasure_mass_le hR k)) hB
    · filter_upwards [fiber_support R k] with q hq
      exact hb q hq.1
  · simp [fiberOutput,fiberMeasure_zero_outside R hk,hk]

def outputCut (s : Set E) (Φ : FourMomenta→ℝ) : FourMomenta→ℝ :=
  ((fun q : FourMomenta=>q 0) ⁻¹' s).indicator Φ

theorem outputCut_measurable {s : Set E} (hs : MeasurableSet s)
    {Φ : FourMomenta→ℝ} (hΦ : Measurable Φ) : Measurable (outputCut s Φ) :=
  hΦ.indicator (hs.preimage (measurable_pi_apply 0))

theorem outputCut_integrable {R : ℝ} {s : Set E} (hs : MeasurableSet s)
    {Φ : FourMomenta→ℝ} (hi : Integrable Φ (pairingMeasure R)) :
    Integrable (outputCut s Φ) (pairingMeasure R) :=
  hi.indicator (hs.preimage (measurable_pi_apply 0))

theorem fiberOutput_cut (R : ℝ) (s : Set E) (Φ : FourMomenta→ℝ) :
    fiberOutput R (outputCut s Φ)=s.indicator (fiberOutput R Φ) := by
  funext k
  by_cases hk : k∈s
  · rw [Set.indicator_of_mem hk]
    apply integral_congr_ae
    filter_upwards [fiber_support R k] with q hq
    exact Set.indicator_of_mem (by simpa only [mem_preimage,hq.2] using hk) Φ
  · rw [Set.indicator_of_notMem hk]
    change (∫q,outputCut s Φ q∂fiberMeasure R k)=0
    apply integral_eq_zero_of_ae
    filter_upwards [fiber_support R k] with q hq
    exact Set.indicator_of_notMem (by simpa only [mem_preimage,hq.2] using hk) Φ

def incomingIntegrand (R : ℝ) (Φ : FourMomenta→ℝ)
    (p : (E×E)×Sphere) : ℝ :=
  (‖p.1.1-p.1.2‖/8)*CoareaNormalization.sharpReadout R Φ
    (IncomingPairMarginal.incomingQuartet p)

def incomingOutput (R : ℝ) (Φ : FourMomenta→ℝ) (k : E) : ℝ :=
  ∫p:E,∫σ:Sphere,incomingIntegrand R Φ ((k,p),σ)∂surface

theorem incomingOutput_integrable (R : ℝ) (Φ : FourMomenta→ℝ) (hΦ : Measurable Φ)
    (hi : Integrable Φ (pairingMeasure R)) : Integrable (incomingOutput R Φ) :=
  (IncomingSignedDisintegration.original_incoming_signed_integrable R Φ hΦ hi).integral_prod_left.integral_prod_left

theorem incomingOutput_integral (R : ℝ) (Φ : FourMomenta→ℝ) (hΦ : Measurable Φ)
    (hi : Integrable Φ (pairingMeasure R)) :
    (∫q,Φ q∂pairingMeasure R)=∫k,incomingOutput R Φ k := by
  rw [IncomingSignedDisintegration.original_incoming_signed_integral R Φ hΦ hi]
  have hi' := IncomingSignedDisintegration.original_incoming_signed_integrable R Φ hΦ hi
  rw [integral_prod _ hi',integral_prod _ hi'.integral_prod_left]
  rfl

theorem incomingOutput_cut (R : ℝ) (s : Set E) (Φ : FourMomenta→ℝ) :
    incomingOutput R (outputCut s Φ)=s.indicator (incomingOutput R Φ) := by
  classical
  funext k
  have hpoint : ∀p σ,incomingIntegrand R (outputCut s Φ) ((k,p),σ)=
      if k∈s then incomingIntegrand R Φ ((k,p),σ) else 0 := by
    intro p σ
    unfold incomingIntegrand CoareaNormalization.sharpReadout outputCut
    by_cases hq : IncomingPairMarginal.incomingQuartet ((k,p),σ)∈
        CoareaNormalization.allFourFlags R
    · simp only [Set.indicator_of_mem hq]
      by_cases hk : k∈s
      · simp only [if_pos hk,Set.indicator_of_mem (show
          IncomingPairMarginal.incomingQuartet ((k,p),σ)∈(fun q : FourMomenta=>q 0) ⁻¹' s from hk)]
      · simp only [if_neg hk,Set.indicator_of_notMem (show
          IncomingPairMarginal.incomingQuartet ((k,p),σ)∉(fun q : FourMomenta=>q 0) ⁻¹' s from hk),mul_zero]
    · simp only [Set.indicator_of_notMem hq,mul_zero,ite_self]
  by_cases hk : k∈s
  · rw [Set.indicator_of_mem hk]
    simp only [incomingOutput,hpoint,if_pos hk]
  · rw [Set.indicator_of_notMem hk]
    simp only [incomingOutput,hpoint,if_neg hk,integral_zero]

theorem original_incoming_fiber_ae {R B : ℝ} (hR : 0≤R) (hB : 0≤B)
    (Φ : FourMomenta→ℝ) (hΦ : Measurable Φ)
    (hb : ∀q∈CoareaNormalization.allFourFlags R,‖Φ q‖≤B) :
    fiberOutput R Φ=ᵐ[volume]incomingOutput R Φ := by
  have hi := bounded_joint_integrable hR Φ hΦ hb
  apply Integrable.ae_eq_of_forall_setIntegral_eq _ _
    (fiberOutput_integrable hR hB Φ hΦ hb) (incomingOutput_integrable R Φ hΦ hi)
  intro s hs _
  rw [←integral_indicator hs,←integral_indicator hs,
    ←fiberOutput_cut R s Φ,←incomingOutput_cut R s Φ]
  exact (collisionKernel_joint_integral hR _ (outputCut_integrable hs hi)).symm.trans
    (incomingOutput_integral R _ (outputCut_measurable hs hΦ) (outputCut_integrable hs hi))

def crossIntegrand (R : ℝ) (Φ : FourMomenta→ℝ)
    (p : (E×E)×PlaneCoarea.E2) : ℝ :=
  (2*‖p.1.2-p.1.1‖)⁻¹*CoareaNormalization.sharpReadout R Φ
    (CrossPairCoordinates.crossQuartet p)

def crossOutput (R : ℝ) (Φ : FourMomenta→ℝ) (k : E) : ℝ :=
  ∫p:E,∫z:PlaneCoarea.E2,crossIntegrand R Φ ((k,p),z)

theorem crossOutput_integrable {R : ℝ} (hR : 0≤R) (Φ : FourMomenta→ℝ) (hΦ : Measurable Φ)
    (hi : Integrable Φ (pairingMeasure R)) : Integrable (crossOutput R Φ) :=
  (CrossSignedDisintegration.original_cross_signed_integrable hR Φ hΦ hi).integral_prod_left.integral_prod_left

theorem crossOutput_integral {R : ℝ} (hR : 0≤R) (Φ : FourMomenta→ℝ) (hΦ : Measurable Φ)
    (hi : Integrable Φ (pairingMeasure R)) :
    (∫q,Φ q∂pairingMeasure R)=∫k,crossOutput R Φ k := by
  rw [CrossSignedDisintegration.original_cross_signed_integral hR Φ hΦ hi]
  have hi' := CrossSignedDisintegration.original_cross_signed_integrable hR Φ hΦ hi
  rw [integral_prod _ hi',integral_prod _ hi'.integral_prod_left]
  rfl

theorem crossOutput_cut (R : ℝ) (s : Set E) (Φ : FourMomenta→ℝ) :
    crossOutput R (outputCut s Φ)=s.indicator (crossOutput R Φ) := by
  classical
  funext k
  have hpoint : ∀p z,crossIntegrand R (outputCut s Φ) ((k,p),z)=
      if k∈s then crossIntegrand R Φ ((k,p),z) else 0 := by
    intro p z
    unfold crossIntegrand CoareaNormalization.sharpReadout outputCut
    by_cases hq : CrossPairCoordinates.crossQuartet ((k,p),z)∈CoareaNormalization.allFourFlags R
    · simp only [Set.indicator_of_mem hq]
      by_cases hk : k∈s
      · simp only [if_pos hk,Set.indicator_of_mem (show
          CrossPairCoordinates.crossQuartet ((k,p),z)∈(fun q : FourMomenta=>q 0) ⁻¹' s from
            by simpa only [mem_preimage,CrossPairCoordinates.crossQuartet_first] using hk)]
      · simp only [if_neg hk,Set.indicator_of_notMem (show
          CrossPairCoordinates.crossQuartet ((k,p),z)∉(fun q : FourMomenta=>q 0) ⁻¹' s from
            by simpa only [mem_preimage,CrossPairCoordinates.crossQuartet_first] using hk),mul_zero]
    · simp only [Set.indicator_of_notMem hq,mul_zero,ite_self]
  by_cases hk : k∈s
  · rw [Set.indicator_of_mem hk]
    simp only [crossOutput,hpoint,if_pos hk]
  · rw [Set.indicator_of_notMem hk]
    simp only [crossOutput,hpoint,if_neg hk,integral_zero]

theorem original_cross_fiber_ae {R B : ℝ} (hR : 0≤R) (hB : 0≤B)
    (Φ : FourMomenta→ℝ) (hΦ : Measurable Φ)
    (hb : ∀q∈CoareaNormalization.allFourFlags R,‖Φ q‖≤B) :
    fiberOutput R Φ=ᵐ[volume]crossOutput R Φ := by
  have hi := bounded_joint_integrable hR Φ hΦ hb
  apply Integrable.ae_eq_of_forall_setIntegral_eq _ _
    (fiberOutput_integrable hR hB Φ hΦ hb) (crossOutput_integrable hR Φ hΦ hi)
  intro s hs _
  rw [←integral_indicator hs,←integral_indicator hs,
    ←fiberOutput_cut R s Φ,←crossOutput_cut R s Φ]
  exact (collisionKernel_joint_integral hR _ (outputCut_integrable hs hi)).symm.trans
    (crossOutput_integral hR _ (outputCut_measurable hs hΦ) (outputCut_integrable hs hi))

theorem original_outgoing_fiber_ae {R B : ℝ} (hR : 0≤R) (hB : 0≤B)
    (Φ : FourMomenta→ℝ) (hΦ : Measurable Φ)
    (hb : ∀q∈CoareaNormalization.allFourFlags R,‖Φ q‖≤B) :
    fiberOutput R (Φ ∘ swapOutgoingK)=ᵐ[volume]fiberOutput R Φ := by
  have hΨ := hΦ.comp (outgoing_preserves_pairing R).measurable
  have hbΨ : ∀q∈CoareaNormalization.allFourFlags R,‖(Φ ∘ swapOutgoingK) q‖≤B := by
    intro q hq
    apply hb
    intro i
    fin_cases i <;> exact hq _
  have hi := bounded_joint_integrable hR Φ hΦ hb
  have hiΨ := bounded_joint_integrable hR (Φ ∘ swapOutgoingK) hΨ hbΨ
  apply Integrable.ae_eq_of_forall_setIntegral_eq _ _
    (fiberOutput_integrable hR hB _ hΨ hbΨ) (fiberOutput_integrable hR hB Φ hΦ hb)
  intro s hs _
  rw [←integral_indicator hs,←integral_indicator hs,
    ←fiberOutput_cut R s _,←fiberOutput_cut R s Φ]
  simp only [fiberOutput]
  rw [←collisionKernel_joint_integral hR _ (outputCut_integrable hs hiΨ),
    ←collisionKernel_joint_integral hR _ (outputCut_integrable hs hi)]
  have he : outputCut s (Φ ∘ swapOutgoingK)=(outputCut s Φ) ∘ swapOutgoingK := by
    funext q
    by_cases hq : q 0∈s <;> simp [outputCut,Function.comp_def,swapOutgoingK,hq]
  rw [he]
  simp only [Function.comp_apply]
  rw [←integral_map (outgoing_preserves_pairing R).measurable.aemeasurable
    (outputCut_measurable hs hΦ).aestronglyMeasurable,(outgoing_preserves_pairing R).map_eq]

end
end Resonance.SignedFiberReadout
