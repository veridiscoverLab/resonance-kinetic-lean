import Resonance.CriticalProductKernel

/-! Absolute integrability of the complete critical current before applying
Fubini.  In particular the nested-integral limits do not use the convention
that a nonintegrable Bochner integral is zero. -/
open Set MeasureTheory Filter
open scoped Topology
namespace Resonance.CriticalProductIntegrability
noncomputable section
variable {X E : Type*} [MeasurableSpace X] [NormedAddCommGroup E]
  [NormedSpace ℝ E] [CompleteSpace E]
open ScaledShrinkingKernel CriticalProductKernel

omit [CompleteSpace E] in
theorem complete_section_norm_integral_bound {ρ : ℝ → ℝ} (hρ : Integrable ρ)
    (hpos : ∀ q, 0 ≤ ρ q) (hmass : ∫ q, ρ q = 1)
    {A : ℝ → E} (hA : AEStronglyMeasurable A) {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ q, ‖A q‖ ≤ C) (b : ℝ) :
    (∫ q, ‖b • (ρ (-b*q) • A q)‖) ≤ C := by
  by_cases hb0 : b = 0
  · simp [hb0, hC]
  · have hn := scaled_kernel_bound hρ hpos hmass hA.norm
      (fun q => by simpa only [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)] using hb q)
      (neg_ne_zero.mpr hb0)
    have hp : 0 ≤ ∫ q, ρ (-b*q) * ‖A q‖ := integral_nonneg (fun q =>
      mul_nonneg (hpos _) (norm_nonneg _))
    simp only [smul_eq_mul, Real.norm_eq_abs, abs_of_nonneg hp, abs_neg] at hn
    have he : (∫ q, ‖b • (ρ (-b*q) • A q)‖) =
        |b| * (∫ q, ρ (-b*q) * ‖A q‖) := by
      simp only [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hpos _)]
      exact integral_const_mul _ _
    rw [he]
    have hmul := mul_le_mul_of_nonneg_left hn.2 (abs_nonneg b)
    simpa only [mul_comm, mul_div_cancel₀ C (abs_ne_zero.mpr hb0)] using hmul

omit [CompleteSpace E] in
theorem complete_joint_integrable (μ : Measure X) [IsFiniteMeasure μ]
    {ρ : ℝ → ℝ} (hm : Measurable ρ) (hρ : Integrable ρ)
    (hpos : ∀ q, 0 ≤ ρ q) (hmass : ∫ q, ρ q = 1)
    (b : X → ℝ) (hb : Measurable b) (A : X × ℝ → E) (hA : StronglyMeasurable A)
    {C : ℝ} (hC : 0 ≤ C) (hbound : ∀ p q, ‖A (p,q)‖ ≤ C) :
    Integrable (fun z : X × ℝ => b z.1 • (ρ (-b z.1*z.2) • A z)) (μ.prod volume) := by
  have hg : StronglyMeasurable (fun z : X × ℝ => b z.1 • (ρ (-b z.1*z.2) • A z)) :=
    (hb.comp measurable_fst).stronglyMeasurable.smul
      ((hm.comp (((hb.comp measurable_fst).neg).mul measurable_snd)).stronglyMeasurable.smul hA)
  have hs : ∀ p, StronglyMeasurable (fun q => A (p,q)) := fun p =>
    hA.comp_measurable (measurable_const.prodMk measurable_id)
  apply (integrable_prod_iff hg.aestronglyMeasurable).mpr
  refine ⟨ae_of_all μ (fun p => complete_section_integrable hρ hpos hmass
    (hs p).aestronglyMeasurable (hbound p) (b p)), ?_⟩
  apply (integrable_const C).mono' hg.norm.integral_prod_right'.aestronglyMeasurable
  exact ae_of_all μ (fun p => by
    rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg (fun _ => norm_nonneg _))]
    exact complete_section_norm_integral_bound hρ hpos hmass
      (hs p).aestronglyMeasurable hC (hbound p) (b p))

omit [CompleteSpace E] in
theorem complete_joint_integral_eq (μ : Measure X) [IsFiniteMeasure μ]
    {ρ : ℝ → ℝ} (hm : Measurable ρ) (hρ : Integrable ρ)
    (hpos : ∀ q, 0 ≤ ρ q) (hmass : ∫ q, ρ q = 1)
    (b : X → ℝ) (hb : Measurable b) (A : X × ℝ → E) (hA : StronglyMeasurable A)
    {C : ℝ} (hC : 0 ≤ C) (hbound : ∀ p q, ‖A (p,q)‖ ≤ C) :
    (∫ z : X × ℝ, b z.1 • (ρ (-b z.1*z.2) • A z) ∂μ.prod volume) =
      ∫ p, b p • (∫ q, ρ (-b p*q) • A (p,q)) ∂μ := by
  rw [integral_prod _ (complete_joint_integrable μ hm hρ hpos hmass b hb A hA hC hbound)]
  congr 1
  funext p
  exact integral_smul (b p) (fun q => ρ (-b p*q) • A (p,q))

end
end Resonance.CriticalProductIntegrability
