import Resonance.CoordinateLevelBochner

/-! Actual pinned regular-chart delta limits, with the original Euclidean
coarea and (2π)^(-3) normalization. No mollifier shape or height bound is used. -/
open Set MeasureTheory Filter
open scoped Topology ContDiff
namespace Resonance.PinnedRegularMollifier
noncomputable section
open PinnedMeasure CoordinateReplacement CoordinateLevelCoarea
open PinnedMeasureNormalization
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

theorem chart_limit {d : ℝ} (hd0 : 0<d) (hdU : d<1/2)
    (e : OpenPartialHomeomorph Ambient Ambient)
    (he : (e : Ambient → Ambient)=replace 1 (liftedEnergy d))
    (hinv : ContDiffOn ℝ 1 e.symm e.target)
    (hn : ∀p∈e.source,(fderiv ℝ (liftedEnergy d) p) (CoordinateReplacement.unit 1)≠0)
    {B : Ambient → E} (hB : Continuous B) (hK : HasCompactSupport B)
    (hS : tsupport B⊆e.source) (ρ : ℝ → ℝ → ℝ)
    (hρ : ∀η,0<η→Integrable (ρ η)) (hpos : ∀η,0<η→∀x,0≤ρ η x)
    (hmass : ∀η,0<η→∫x,ρ η x=1)
    (hsupport : ∀η,0<η→∀x,ρ η x≠0→|x|≤η) :
    (∀η,0<η→IntegrableOn (fun p=>ρ η (liftedEnergy d p) • B p) e.source) ∧
    IntegrableOn B (e.source∩{p|liftedEnergy d p=0}) (euclideanLiftedRegularCoarea d) ∧
    Tendsto (fun η=>((2*Real.pi)^3)⁻¹ • ∫p in e.source,ρ η (liftedEnergy d p) • B p)
      (𝓝[>]0) (𝓝 (∫p in e.source∩{p|liftedEnergy d p=0},B p
        ∂euclideanLiftedRegularCoarea d)) := by
  have hFC := (pinned_energy_contDiff_one hd0 hdU).contDiffOn (s:=e.source)
  have hgrad := liftedEnergy_hasFDerivAt hd0 hdU
  have hgm := (energyGradient_continuous hd0 hdU).measurable
  have hcp : 0<(2*Real.pi)^3 := by positivity
  refine ⟨fun η hη=>RegularChartMollifier.source_integrable e he hFC hn hB hK hS (hρ η hη),?_,?_⟩
  · have hi := CoordinateLevelBochner.source_level_integrable hgrad hgm hcp
      e he hFC hinv hn hB hK hS 0
    rw [pinned_zero_measure] at hi
    exact hi
  · have ht := (RegularChartMollifier.source_tendsto e he hFC hn hB hK hS
      ρ hρ hpos hmass hsupport).const_smul (((2*Real.pi)^3)⁻¹)
    have heq := CoordinateLevelBochner.source_level_integral hgrad hgm hcp e he hinv hn B 0
    rw [pinned_zero_measure] at heq
    rw [←heq] at ht
    exact ht

theorem every_regular_middle_chart {d : ℝ} (hd0 : 0<d) (hdU : d<1/2)
    (p : Ambient) (hy : energyGradient d p 1≠0) :
    ∃ e : OpenPartialHomeomorph Ambient Ambient, ∃ r : ℝ,
      0<r ∧ e.source=Metric.ball p r ∧
      ∀ (B : Ambient → E), Continuous B → HasCompactSupport B → tsupport B⊆e.source →
      ∀ (ρ : ℝ → ℝ → ℝ),
      (∀η,0<η→Integrable (ρ η)) → (∀η,0<η→∀x,0≤ρ η x) →
      (∀η,0<η→∫x,ρ η x=1) → (∀η,0<η→∀x,ρ η x≠0→|x|≤η) →
      (∀η,0<η→IntegrableOn (fun z=>ρ η (liftedEnergy d z) • B z) e.source) ∧
      IntegrableOn B (e.source∩{z|liftedEnergy d z=0}) (euclideanLiftedRegularCoarea d) ∧
      Tendsto (fun η=>((2*Real.pi)^3)⁻¹ • ∫z in e.source,ρ η (liftedEnergy d z) • B z)
        (𝓝[>]0) (𝓝 (∫z in e.source∩{z|liftedEnergy d z=0},B z
          ∂euclideanLiftedRegularCoarea d)) := by
  have hn : (fderiv ℝ (liftedEnergy d) p) (CoordinateReplacement.unit 1)≠0 := by
    simpa only [gradient_partial (liftedEnergy_hasFDerivAt hd0 hdU)] using hy
  obtain ⟨e,r,δ,he,hr,hδ,hsource,_,hinv,hjac⟩ :=
    ControlledCoordinateChart.exists_chart (pinned_energy_contDiff_one hd0 hdU).contDiffAt 1 hn
  refine ⟨e,r,hr,hsource,?_⟩
  intro B hB hK hS ρ hρ hp hm hs
  exact chart_limit hd0 hdU e he hinv (fun x hx=>abs_pos.mp (hδ.trans_le (hjac x hx)))
    hB hK hS ρ hρ hp hm hs

end
end Resonance.PinnedRegularMollifier
