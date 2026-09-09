import Resonance.RegularPointMollifier

/-! Every regular point of the original pinned resonance has its original
normalized local delta limit, regardless of which partial derivative is nonzero. -/
open Set MeasureTheory Filter
open scoped Topology
namespace Resonance.PinnedRegularPoint
noncomputable section
open PinnedMeasure PinnedMeasureNormalization
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

theorem every_regular_point {d : ℝ} (hd0 : 0<d) (hdU : d<1/2)
    (p : Ambient) (hn : energyGradient d p≠0) :
    ∃ S : Set Ambient, IsOpen S ∧ p∈S ∧
      ∀ (B : Ambient → E), Continuous B → HasCompactSupport B → tsupport B⊆S →
      ∀ (ρ : ℝ → ℝ → ℝ),
      (∀η,0<η→Integrable (ρ η)) → (∀η,0<η→∀x,0≤ρ η x) →
      (∀η,0<η→∫x,ρ η x=1) → (∀η,0<η→∀x,ρ η x≠0→|x|≤η) →
      (∀η,0<η→IntegrableOn (fun z=>ρ η (liftedEnergy d z) • B z) S) ∧
      IntegrableOn B (S∩{z|liftedEnergy d z=0}) (euclideanLiftedRegularCoarea d) ∧
      Tendsto (fun η=>((2*Real.pi)^3)⁻¹ • ∫z in S,ρ η (liftedEnergy d z) • B z)
        (𝓝[>]0) (𝓝 (∫z in S∩{z|liftedEnergy d z=0},B z
          ∂euclideanLiftedRegularCoarea d)) :=
  RegularPointMollifier.every_regular_point (liftedEnergy_hasFDerivAt hd0 hdU)
    (CoordinateLevelCoarea.pinned_energy_contDiff_one hd0 hdU)
    (energyGradient_continuous hd0 hdU).measurable (by positivity) p hn

end
end Resonance.PinnedRegularPoint
