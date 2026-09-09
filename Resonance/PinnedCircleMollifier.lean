import Resonance.PinnedPeriodicCompleteLimit
import Resonance.PinnedCellHaar
import Resonance.PinnedSmoothDomain

/-! Exact original circle regularization, for the full signed four-leg
difference and arbitrary continuous common source. The left measure is the
product of the three original probability Haar measures. -/
open Set MeasureTheory Filter
open scoped ContDiff Topology
namespace Resonance.PinnedCircleMollifier
noncomputable section
open PinnedMeasure PinnedPeriodicity PinnedCompactLocalization PinnedMeasureNormalization
open PinnedClassificationFinal PinnedEndToEnd PinnedLegACCircle PinnedMaximalDifference
open PinnedSmoothDomain PinnedCriticalCancellation
local instance periodPositive : Fact (0<period) := ⟨period_pos⟩

def energy (d : ℝ) (k : CircleMomenta) : ℝ :=
  circleDispersion d (circleLeg 0 k)+circleDispersion d (circleLeg 1 k)-
    circleDispersion d (circleLeg 2 k)-circleDispersion d (circleLeg 3 k)

theorem energy_continuous {d : ℝ} (hd0 : 0<d) (hdU : d<1/2) : Continuous (energy d) := by
  have h := circleDispersion_continuous hd0 hdU
  exact (((h.comp (circleLeg_continuous 0)).add (h.comp (circleLeg_continuous 1))).sub
    (h.comp (circleLeg_continuous 2))).sub (h.comp (circleLeg_continuous 3))

theorem energy_quotient (d : ℝ) (k : Ambient) :
    energy d (quotientCoordinates k)=liftedEnergy d k := by
  change circleDispersion d (k 0:PinnedPeriodicity.Circle)+
    circleDispersion d (k 1:PinnedPeriodicity.Circle)-circleDispersion d (k 2:PinnedPeriodicity.Circle)-
    circleDispersion d ((k 0+k 1-k 2:ℝ):PinnedPeriodicity.Circle)=_
  simp only [circleDispersion_coe]
  rfl

theorem complete_source_limit {d : ℝ} (hd0 : 0<d) (hdU : d<1/2)
    {φ : PinnedPeriodicity.Circle→ℂ} (hφ : Continuous φ)
    (hφ2 : ContDiff ℝ 2 (periodicLift φ))
    {W : CircleMomenta→ℂ} (hW : Continuous W)
    (ρ : ℝ → ℝ → ℝ) (hm : ∀η,0<η→Measurable (ρ η))
    (hρ : ∀η,0<η→Integrable (ρ η)) (hpos : ∀η,0<η→∀q,0≤ρ η q)
    (hmass : ∀η,0<η→∫q,ρ η q=1)
    (hs : ∀η,0<η→∀q,ρ η q≠0→|q|≤η) :
    (∀ᶠη in 𝓝[>]0,Integrable
      (fun k=>ρ η (energy d k) • (W k*difference φ k))
      (Measure.pi (fun _:Fin 3=>circleHaar))) ∧
    Integrable (fun k=>W k*difference φ k) (euclideanCircleRegularCoarea d) ∧
    Tendsto (fun η=>∫k,ρ η (energy d k) • (W k*difference φ k)
      ∂Measure.pi (fun _:Fin 3=>circleHaar)) (𝓝[>]0)
      (𝓝 (∫k,W k*difference φ k ∂euclideanCircleRegularCoarea d)) := by
  have hpW : ∀n k,(W ∘ quotientCoordinates) (translation n k)=
      (W ∘ quotientCoordinates) k := by
    intro n k
    simp only [Function.comp_apply,quotient_translation]
  obtain ⟨hv,hc,hl⟩ := PinnedPeriodicCompleteLimit.periodic_complete_source_limit
    hd0 hdU hφ2 (periodicLift_periodic φ) (hW.comp quotientCoordinates_continuous)
    hpW ρ hm hρ hpos hmass hs
  have hB : Continuous (fun k=>W k*difference φ k) := hW.mul (difference_continuous hφ)
  have hmeas : ∀η,0<η→Measurable (fun k=>ρ η (energy d k) • (W k*difference φ k)) := by
    intro η hη
    simpa only [Complex.real_smul] using
      (Complex.measurable_ofReal.comp ((hm η hη).comp
        (energy_continuous hd0 hdU).measurable)).mul hB.measurable
  have hiC : Integrable (fun k=>W k*difference φ k) (euclideanCircleRegularCoarea d) := by
    apply (integrable_map_measure hB.aestronglyMeasurable
      quotientCoordinates_continuous.measurable.aemeasurable).mpr
    simpa only [Function.comp_apply,difference_quotient] using hc
  have heC : (∫k,W k*difference φ k ∂euclideanCircleRegularCoarea d)=
      ∫k,(W ∘ quotientCoordinates) k*fullDifference (periodicLift φ) k
        ∂euclideanCellCoarea d := by
    rw [euclideanCircleRegularCoarea,integral_map
      quotientCoordinates_continuous.measurable.aemeasurable hB.aestronglyMeasurable]
    simp only [Function.comp_apply,difference_quotient]
  have heV : ∀η,0<η→(∫k,ρ η (energy d k) • (W k*difference φ k)
      ∂Measure.pi (fun _:Fin 3=>circleHaar))=
      (period^3)⁻¹ • ∫k in fundamentalCell,
        ρ η (liftedEnergy d k) • ((W ∘ quotientCoordinates) k*
          fullDifference (periodicLift φ) k) := by
    intro η hη
    simpa only [energy_quotient,difference_quotient,Function.comp_apply] using
      PinnedCellHaar.probability_cell_integral _ (hmeas η hη).aestronglyMeasurable
  refine ⟨?_,hiC,?_⟩
  · filter_upwards [hv,self_mem_nhdsWithin] with η hi hη
    apply PinnedCellHaar.probability_cell_integrable (hmeas η hη).aestronglyMeasurable
    simpa only [energy_quotient,difference_quotient,Function.comp_apply] using hi
  · rw [heC]
    apply hl.congr'
    filter_upwards [self_mem_nhdsWithin] with η hη
    exact (heV η hη).symm

end
end Resonance.PinnedCircleMollifier
