import Resonance.RNTestFunctions
import Resonance.PinnedWeightedReadings

/-! One original L¹ output simultaneously represents every continuous test.
The density is selected before the test, from the full signed current. -/
open Set MeasureTheory Filter
open scoped ContDiff
namespace Resonance.PinnedRNReadings
noncomputable section
open PinnedPeriodicity PinnedClassificationFinal PinnedMeasureNormalization PinnedLegACCircle
open PinnedMaximalDifference PinnedSmoothDomain PinnedWeakIntegrability PinnedWeakOutputL1
open PinnedQuarterSymmetrization PinnedWeightedReadings
local instance periodPositive : Fact (0<period) := ⟨period_pos⟩

theorem tested_output {d : ℝ} (hd0 : 0<d) (hdU : d<1/2)
    {a : FourCircle→ℝ} (ha : Continuous a)
    {φ : PinnedPeriodicity.Circle→ℂ} (hφ : Continuous φ)
    (hφ2 : ContDiff ℝ 2 (periodicLift φ)) (γ : ℝ) (i : Fin 4)
    {g : PinnedPeriodicity.Circle→ℂ} (hg : Integrable g circleHaar)
    (he : ∀s,MeasurableSet s→(∫x in s,g x∂circleHaar)=
      ∫k in (circleLeg i)⁻¹' s,(γ:ℂ)*difference φ k∂weightedCoarea d a)
    (ψ : C(PinnedPeriodicity.Circle,ℂ)) :
    (∫x,star (ψ x)*g x∂circleHaar)=
      (γ:ℂ)*(∫k,difference φ k*star (ψ (circleLeg i k))∂weightedCoarea d a) := by
  have hi : Integrable ((γ:ℂ) • difference φ) (weightedCoarea d a) :=
    ((integrable_norm_iff (difference_continuous hφ).aestronglyMeasurable).mp
      (difference_norm_integrable_weighted hd0 hdU ha hφ hφ2)).const_mul (γ:ℂ)
  have hp := RNTestFunctions.bounded_test (weightedCoarea d a) circleHaar
    (circleLeg_continuous i).measurable hi hg he ψ.continuous.star.measurable
    (norm_nonneg ψ) (fun x=>by
      simpa only [norm_star] using ContinuousMap.norm_coe_le_norm ψ x)
  refine hp.2.2.trans ?_
  calc
    _ = ∫k,(γ:ℂ)*(difference φ k*star (ψ (circleLeg i k)))∂weightedCoarea d a := by
      apply integral_congr_ae
      exact Eventually.of_forall (fun k=>by
        change star (ψ (circleLeg i k))*((γ:ℂ)*difference φ k)=
          (γ:ℂ)*(difference φ k*star (ψ (circleLeg i k)))
        ring)
    _ = _ := integral_const_mul _ _

theorem exists_all_tested_output {d : ℝ} (hd0 : 0<d) (hdU : d<1/2)
    {a : FourCircle→ℝ} (ha : Continuous a)
    {φ : PinnedPeriodicity.Circle→ℂ} (hφ : Continuous φ)
    (hφ2 : ContDiff ℝ 2 (periodicLift φ)) (γ : ℝ) (i : Fin 4) :
    ∃g:PinnedPeriodicity.Circle→ℂ,Integrable g circleHaar ∧
      (∀s,MeasurableSet s→(∫x in s,g x∂circleHaar)=
        ∫k in (circleLeg i)⁻¹' s,(γ:ℂ)*difference φ k∂weightedCoarea d a) ∧
      ∀ψ:C(PinnedPeriodicity.Circle,ℂ),(∫x,star (ψ x)*g x∂circleHaar)=
        (γ:ℂ)*(∫k,difference φ k*star (ψ (circleLeg i k))∂weightedCoarea d a) := by
  obtain ⟨g,hg,he⟩ := exists_L1_weak_output hd0 hdU ha hφ hφ2 γ i
  exact ⟨g,hg,he,tested_output hd0 hdU ha hφ hφ2 γ i hg he⟩

end
end Resonance.PinnedRNReadings
