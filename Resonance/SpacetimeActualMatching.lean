import Resonance.SpacetimeSourceProducts
import Resonance.ContinuousMicroscopicMatching

/-! The joint-space five-moment constraint comes from the moments of the
same actual distribution at (t,X). The matched parameter is the already
constructed inverse moment map, not an independently supplied macro field.
Measurability and finite uniform bounds of the displayed continuous families
are ordinary source membership inputs, not convergence or matching premises. -/
open Set MeasureTheory MeasureTheory.Measure
namespace Resonance.SpacetimeActualMatching
noncomputable section
open ResonantMeasure Thermodynamics ThermodynamicChart SpacetimePairing
open SpacetimeReference SpacetimeContinuousFields SpacetimeSourceProducts
open ContinuousMicroscopicFields ProfileBanachSmooth ActualMatchedMoments
open ProductL2Slices LpOperators PhysicalFiveBasis

def cubeFamily {R : ℝ} (f : ℝ→FreeTransport.Distribution R) (a : Base) : C(cube R,ℝ) :=
  (f a.1).curry a.2

def matchedFamily {R : ℝ} (hR : 0<R) (f : ℝ→FreeTransport.Distribution R) (a : Base) : Parameter :=
  matchedValue R hR (f a.1) a.2

def yFamily {R : ℝ} (hR : 0<R) (c : ℝ) (f : ℝ→FreeTransport.Distribution R)
    (θ : Base→Parameter) (a : Base) : C(cube R,ℝ) :=
  yField c (cubeFamily f a) (profileMap R (θ a)) (profileMap R (matchedFamily hR f a))

def bFamily {R : ℝ} (hR : 0<R) (f : ℝ→FreeTransport.Distribution R)
    (θ : Base→Parameter) (a : Base) : C(cube R,ℝ) :=
  bField (cubeFamily f a) (profileMap R (θ a)) (profileMap R (matchedFamily hR f a))

set_option backward.isDefEq.respectTransparency false in
theorem actual_weighted_constraint {R : ℝ} (hR : 0<R) (T c : ℝ)
    (f : ℝ→FreeTransport.Distribution R) (θ : Base→Parameter)
    {CB CY : ℝ} (hCB : 0≤CB)
    (hBm : Measurable (bFamily hR f θ)) (hYm : Measurable (yFamily hR c f θ))
    (hB : ∀ᵐa∂baseMeasure T,‖bFamily hR f θ a‖≤CB)
    (hY : ∀ᵐa∂baseMeasure T,‖yFamily hR c f θ a‖≤CY)
    (hf : ∀ᵐa∂baseMeasure T,∀k,(f a.1) (a.2,k)≠0)
    (hU : ∀ᵐa∂baseMeasure T,actualMoments R (f a.1) a.2∈momentImage R) :
    ∀ᵐa∂baseMeasure T,∀ha:θ a∈positiveDomain R,
      analysisMap hR ha
        (slice (multiplyCLM (family_coefficient_memLp T hBm hB)
          (source hR.le T hYm hY)) a)=0 := by
  filter_upwards [product_source_slice_ae hR T hCB hBm hYm hB hY,hf,hU]
    with a hs hf hU
  intro ha
  have hp:=ContinuousMicroscopicMatching.actual_matched_weighted_constraint hR c
    (f a.1) a.2 hf hU ha
  rw [ContinuousSourceMultiplication.multiplier_sourceMap] at hp
  erw [hs]
  exact hp

theorem actual_original_moments {R : ℝ} (hR : 0<R)
    (f : ℝ→FreeTransport.Distribution R) (a : Base)
    (hU : actualMoments R (f a.1) a.2∈momentImage R) :
    momentMap R (matchedFamily hR f a)=actualMoments R (f a.1) a.2 :=
  momentInverse_right R hR _ hU

end
end Resonance.SpacetimeActualMatching
