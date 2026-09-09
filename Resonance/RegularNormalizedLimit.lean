import Resonance.CoordinateLevelBochner

/-! The full normalized regular-chart limit for an actual C1 level function
and its actual gradient; no area or delta identity is a premise. -/
open Set MeasureTheory Filter
open scoped Topology ContDiff InnerProductSpace
namespace Resonance.RegularNormalizedLimit
noncomputable section
open LinearSurfaceArea CoordinateReplacement RegularGraphCoarea
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

theorem chart_limit {F : A → ℝ} {g : A → A} {c : ℝ}
    (hF : ∀p,HasFDerivAt F (innerSL ℝ (g p)) p) (hg : Measurable g) (hc : 0<c)
    (e : OpenPartialHomeomorph A A) (he : (e : A → A)=replace 1 F)
    (hFC : ContDiffOn ℝ 1 F e.source) (hinv : ContDiffOn ℝ 1 e.symm e.target)
    (hn : ∀p∈e.source,(fderiv ℝ F p) (CoordinateReplacement.unit 1)≠0)
    {B : A → E} (hB : Continuous B) (hK : HasCompactSupport B)
    (hS : tsupport B⊆e.source) (ρ : ℝ → ℝ → ℝ)
    (hρ : ∀η,0<η→Integrable (ρ η)) (hpos : ∀η,0<η→∀x,0≤ρ η x)
    (hmass : ∀η,0<η→∫x,ρ η x=1)
    (hsupport : ∀η,0<η→∀x,ρ η x≠0→|x|≤η) :
    (∀η,0<η→IntegrableOn (fun p=>ρ η (F p) • B p) e.source) ∧
    IntegrableOn B (e.source∩{p|F p=0}) (regularMeasure F g c) ∧
    Tendsto (fun η=>c⁻¹ • ∫p in e.source,ρ η (F p) • B p)
      (𝓝[>]0) (𝓝 (∫p in e.source∩{p|F p=0},B p ∂regularMeasure F g c)) := by
  refine ⟨fun η hη=>RegularChartMollifier.source_integrable e he hFC hn hB hK hS (hρ η hη),?_,?_⟩
  · simpa only [sub_zero] using CoordinateLevelBochner.source_level_integrable hF hg hc
      e he hFC hinv hn hB hK hS 0
  · have ht := (RegularChartMollifier.source_tendsto e he hFC hn hB hK hS
      ρ hρ hpos hmass hsupport).const_smul (c⁻¹)
    have heq := CoordinateLevelBochner.source_level_integral hF hg hc e he hinv hn B 0
    simp only [sub_zero] at heq
    rw [←heq] at ht
    exact ht

end
end Resonance.RegularNormalizedLimit
