import Resonance.ScaledShrinkingKernel
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! Dominated limits of the complete one- and two-factor currents at F=-bq.
Taking the actual b(u,v)=uv gives the two critical integrals in the paper.
The remaining chart change of variables is not assumed to follow from this lemma. -/
open Set MeasureTheory Filter
open scoped Topology
namespace Resonance.CriticalProductKernel
noncomputable section
variable {X E:Type*} [MeasurableSpace X] [NormedAddCommGroup E]
  [NormedSpace ℝ E] [CompleteSpace E]
open ScaledShrinkingKernel

omit [CompleteSpace E] in
theorem complete_section_integrable {ρ:ℝ→ℝ} (hρ:Integrable ρ)
    (hpos:∀q,0≤ρ q) (hmass:∫q,ρ q=1)
    {A:ℝ→E} (hA:AEStronglyMeasurable A) {C:ℝ} (hb:∀q,‖A q‖≤C) (b:ℝ) :
    Integrable (fun q=>b • (ρ (-b*q) • A q)) := by
  by_cases hb0:b=0
  · simp [hb0]
  · exact ((scaled_kernel_bound hρ hpos hmass hA hb (neg_ne_zero.mpr hb0)).1).smul b

omit [CompleteSpace E] in
theorem current_stronglyMeasurable (b:X→ℝ) (hb:Measurable b)
    {ρ:ℝ→ℝ} (hρ:Measurable ρ) {A:X×ℝ→E} (hA:StronglyMeasurable A) :
    StronglyMeasurable (fun p=>b p • (∫q,ρ (-b p*q) • A (p,q))) := by
  have hm:Measurable (fun z:X×ℝ=>ρ (-b z.1*z.2)):=
    hρ.comp (((hb.comp measurable_fst).neg).mul measurable_snd)
  have hi:StronglyMeasurable (fun p=>∫q,ρ (-b p*q) • A (p,q)):=
    (hm.stronglyMeasurable.smul hA).integral_prod_right'
  exact hb.stronglyMeasurable.smul hi

theorem complete_linear_integral_tendsto (μ:Measure X) [IsFiniteMeasure μ]
    (ρ:ℝ→ℝ→ℝ) (hρm:∀η,0<η→Measurable (ρ η))
    (hρ:∀η,0<η→Integrable (ρ η)) (hpos:∀η,0<η→∀q,0≤ρ η q)
    (hmass:∀η,0<η→∫q,ρ η q=1)
    (hsupport:∀η,0<η→∀q,ρ η q≠0→|q|≤η)
    (b:X→ℝ) (hb:Measurable b) (A:X×ℝ→E) (hA:StronglyMeasurable A)
    (hc:∀p,ContinuousAt (fun q=>A (p,q)) 0)
    {C:ℝ} (hC:0≤C) (hbound:∀p q,‖A (p,q)‖≤C) :
    Tendsto (fun η=>∫p,b p • (∫q,ρ η (-b p*q) • A (p,q)) ∂μ) (𝓝[>]0)
      (𝓝 (∫p,(b p/|b p|) • A (p,0) ∂μ)) := by
  have hsec:∀p,StronglyMeasurable (fun q=>A (p,q)):=fun p=>
    hA.comp_measurable (measurable_const.prodMk measurable_id)
  apply tendsto_integral_filter_of_dominated_convergence (fun _=>C)
  · filter_upwards [self_mem_nhdsWithin] with η hη
    exact (current_stronglyMeasurable b hb (hρm η hη) hA).aestronglyMeasurable
  · filter_upwards [self_mem_nhdsWithin] with η hη
    exact ae_of_all μ (fun p=>complete_linear_factor_bound (hρ η hη) (hpos η hη)
      (hmass η hη) (hsec p).aestronglyMeasurable hC (hbound p) (b p))
  · exact integrable_const C
  · exact ae_of_all μ (fun p=>complete_linear_factor_tendsto ρ hρ hpos hmass hsupport
      (hsec p) (hc p) (b p))

theorem complete_quadratic_integral_tendsto (μ:Measure X)
    (ρ:ℝ→ℝ→ℝ) (hρm:∀η,0<η→Measurable (ρ η))
    (hρ:∀η,0<η→Integrable (ρ η)) (hpos:∀η,0<η→∀q,0≤ρ η q)
    (hmass:∀η,0<η→∫q,ρ η q=1)
    (hsupport:∀η,0<η→∀q,ρ η q≠0→|q|≤η)
    (b:X→ℝ) (hb:Measurable b) (hbi:Integrable b μ)
    (A:X×ℝ→E) (hA:StronglyMeasurable A) (hc:∀p,ContinuousAt (fun q=>A (p,q)) 0)
    {C:ℝ} (hC:0≤C) (hbound:∀p q,‖A (p,q)‖≤C) :
    Tendsto (fun η=>∫p,(b p)^2 • (∫q,ρ η (-b p*q) • A (p,q)) ∂μ) (𝓝[>]0)
      (𝓝 (∫p,|b p| • A (p,0) ∂μ)) := by
  have hsec:∀p,StronglyMeasurable (fun q=>A (p,q)):=fun p=>
    hA.comp_measurable (measurable_const.prodMk measurable_id)
  apply tendsto_integral_filter_of_dominated_convergence (fun p=>C*|b p|)
  · filter_upwards [self_mem_nhdsWithin] with η hη
    have hm:Measurable (fun z:X×ℝ=>ρ η (-b z.1*z.2)):=
      (hρm η hη).comp (((hb.comp measurable_fst).neg).mul measurable_snd)
    have hi:StronglyMeasurable (fun p=>∫q,ρ η (-b p*q) • A (p,q)):=
      (hm.stronglyMeasurable.smul hA).integral_prod_right'
    exact ((hb.pow_const 2).stronglyMeasurable.smul hi).aestronglyMeasurable
  · filter_upwards [self_mem_nhdsWithin] with η hη
    exact ae_of_all μ (fun p=>complete_quadratic_factor_bound (hρ η hη) (hpos η hη)
      (hmass η hη) (hsec p).aestronglyMeasurable hC (hbound p) (b p))
  · simpa only [Real.norm_eq_abs] using hbi.norm.const_mul C
  · exact ae_of_all μ (fun p=>complete_quadratic_factor_tendsto ρ hρ hpos hmass hsupport
      (hsec p) (hc p) (b p))

end
end Resonance.CriticalProductKernel
