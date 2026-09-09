import Resonance.CompactRegularMollifier
import Resonance.PinnedRegularPoint

/-! Original pinned compact-source delta limit in the regular region, with an
actually constructed finite source partition and original coarea normalization. -/
open Set MeasureTheory Filter
open scoped Topology
namespace Resonance.PinnedCompactRegular
noncomputable section
open PinnedMeasure PinnedMeasureNormalization
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

theorem compact_regular_limit {d : ℝ} (hd0 : 0<d) (hdU : d<1/2)
    {B : Ambient → E} (hB : Continuous B) (hK : HasCompactSupport B)
    (hreg : ∀p∈tsupport B,energyGradient d p≠0) (ρ : ℝ → ℝ → ℝ)
    (hρ : ∀η,0<η→Integrable (ρ η)) (hpos : ∀η,0<η→∀x,0≤ρ η x)
    (hmass : ∀η,0<η→∫x,ρ η x=1)
    (hsupport : ∀η,0<η→∀x,ρ η x≠0→|x|≤η) :
    (∀η,0<η→Integrable (fun p=>ρ η (liftedEnergy d p) • B p)) ∧
    Integrable B (euclideanLiftedRegularCoarea d) ∧
    Tendsto (fun η=>((2*Real.pi)^3)⁻¹ • ∫p,ρ η (liftedEnergy d p) • B p)
      (𝓝[>]0) (𝓝 (∫p,B p ∂euclideanLiftedRegularCoarea d)) :=
  CompactRegularMollifier.compact_regular_limit (liftedEnergy_hasFDerivAt hd0 hdU)
    (CoordinateLevelCoarea.pinned_energy_contDiff_one hd0 hdU)
    (energyGradient_continuous hd0 hdU).measurable (by positivity)
    hB hK hreg ρ hρ hpos hmass hsupport

end
end Resonance.PinnedCompactRegular
