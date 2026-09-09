import Resonance.ShrinkingKernel

/-! The actual scaled integrals occurring at F=-uvq. The kernel remains the
given, potentially non-even and arbitrarily tall, nonnegative unit-mass family. -/
open Set MeasureTheory Filter
open scoped Topology
namespace Resonance.ScaledShrinkingKernel
noncomputable section
variable {E:Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

omit [CompleteSpace E] in
theorem kernel_mass_bound {ρ:ℝ→ℝ} (hρ:Integrable ρ) (hpos:∀x,0≤ρ x)
    {A:ℝ→E} (hA:AEStronglyMeasurable A) {C:ℝ} (hb:∀x,‖A x‖≤C) :
    Integrable (fun x=>ρ x • A x) ∧ ‖∫x,ρ x • A x‖≤C*(∫x,ρ x) := by
  have hi:Integrable (fun x=>ρ x • A x):=by
    apply (hρ.norm.const_mul C).mono' (hρ.aestronglyMeasurable.smul hA)
    filter_upwards [] with x
    rw [norm_smul]
    simpa only [mul_comm] using mul_le_mul_of_nonneg_left (hb x) (norm_nonneg (ρ x))
  refine ⟨hi,?_⟩
  calc
    _ ≤ ∫x,‖ρ x • A x‖:=norm_integral_le_integral_norm _
    _ ≤ ∫x,C*ρ x:=by
      apply integral_mono_ae hi.norm (hρ.const_mul C)
      filter_upwards [] with x
      rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (hpos x)]
      simpa only [mul_comm] using mul_le_mul_of_nonneg_left (hb x) (hpos x)
    _ = _:=integral_const_mul C ρ

omit [CompleteSpace E] in
theorem scaled_integral_eq {b:ℝ} (hb:b≠0) (ρ:ℝ→ℝ) (A:ℝ→E) :
    (∫q,ρ (b*q) • A q)=|b|⁻¹ • (∫s,ρ s • A (b⁻¹*s)) := by
  have h:=Measure.integral_comp_mul_left (fun s=>ρ s • A (b⁻¹*s)) b
  simpa only [←mul_assoc,inv_mul_cancel₀ hb,one_mul,abs_inv] using h

theorem scaled_kernel_tendsto (ρ:ℝ→ℝ→ℝ)
    (hρ:∀η,0<η→Integrable (ρ η)) (hpos:∀η,0<η→∀x,0≤ρ η x)
    (hmass:∀η,0<η→∫x,ρ η x=1)
    (hsupport:∀η,0<η→∀x,ρ η x≠0→|x|≤η)
    {A:ℝ→E} (hA:StronglyMeasurable A) (hc:ContinuousAt A 0)
    {b:ℝ} (hb:b≠0) :
    Tendsto (fun η=>∫q,ρ η (b*q) • A q) (𝓝[>]0) (𝓝 (|b|⁻¹ • A 0)) := by
  have hc':ContinuousAt (fun s=>A (b⁻¹*s)) 0:=by
    have hmap:ContinuousAt (fun s:ℝ=>b⁻¹*s) 0:=by fun_prop
    exact hc.comp_of_eq hmap (by simp)
  have h:=ShrinkingKernel.arbitrary_kernel_tendsto ρ hρ hpos hmass hsupport
    ((hA.comp_measurable (by fun_prop:Measurable (fun s:ℝ=>b⁻¹*s))).aestronglyMeasurable) hc'
  have ht:=h.const_smul (|b|⁻¹)
  simpa only [Function.comp_apply,mul_zero,←scaled_integral_eq hb] using ht

omit [CompleteSpace E] in
theorem scaled_kernel_bound {ρ:ℝ→ℝ} (hρ:Integrable ρ)
    (hpos:∀x,0≤ρ x) (hmass:∫x,ρ x=1)
    {A:ℝ→E} (hA:AEStronglyMeasurable A) {C:ℝ} (hbound:∀x,‖A x‖≤C)
    {b:ℝ} (hb:b≠0) :
    Integrable (fun q=>ρ (b*q) • A q) ∧ ‖∫q,ρ (b*q) • A q‖≤C/|b| := by
  have h:=kernel_mass_bound (hρ.comp_mul_left' hb) (fun q=>hpos (b*q)) hA hbound
  rw [Measure.integral_comp_mul_left ρ b,hmass,smul_eq_mul,mul_one,abs_inv] at h
  simpa only [div_eq_mul_inv] using h

omit [CompleteSpace E] in
theorem complete_linear_factor_bound {ρ:ℝ→ℝ} (hρ:Integrable ρ)
    (hpos:∀x,0≤ρ x) (hmass:∫x,ρ x=1)
    {A:ℝ→E} (hA:AEStronglyMeasurable A) {C:ℝ} (hC:0≤C) (hbound:∀x,‖A x‖≤C)
    (b:ℝ) : ‖b • (∫q,ρ (-b*q) • A q)‖≤C := by
  by_cases hb:b=0
  · simp [hb,hC]
  · have h:‖∫q,ρ (-b*q) • A q‖≤C/|b|:=by
      simpa only [abs_neg] using (scaled_kernel_bound hρ hpos hmass hA hbound (neg_ne_zero.mpr hb)).2
    rw [norm_smul,Real.norm_eq_abs]
    have hp:0 < |b|:=abs_pos.mpr hb
    have hmul:=mul_le_mul_of_nonneg_left h hp.le
    simpa only [mul_div_cancel₀ C (ne_of_gt hp),mul_comm] using hmul

omit [CompleteSpace E] in
theorem complete_quadratic_factor_bound {ρ:ℝ→ℝ} (hρ:Integrable ρ)
    (hpos:∀x,0≤ρ x) (hmass:∫x,ρ x=1)
    {A:ℝ→E} (hA:AEStronglyMeasurable A) {C:ℝ} (hC:0≤C) (hbound:∀x,‖A x‖≤C)
    (b:ℝ) : ‖(b^2) • (∫q,ρ (-b*q) • A q)‖≤C*|b| := by
  have h:=complete_linear_factor_bound hρ hpos hmass hA hC hbound b
  rw [pow_two,mul_smul,norm_smul,Real.norm_eq_abs]
  simpa only [mul_comm] using mul_le_mul_of_nonneg_left h (abs_nonneg b)

theorem complete_linear_factor_tendsto (ρ:ℝ→ℝ→ℝ)
    (hρ:∀η,0<η→Integrable (ρ η)) (hpos:∀η,0<η→∀x,0≤ρ η x)
    (hmass:∀η,0<η→∫x,ρ η x=1)
    (hsupport:∀η,0<η→∀x,ρ η x≠0→|x|≤η)
    {A:ℝ→E} (hA:StronglyMeasurable A) (hc:ContinuousAt A 0) (b:ℝ) :
    Tendsto (fun η=>b • (∫q,ρ η (-b*q) • A q)) (𝓝[>]0) (𝓝 ((b/|b|) • A 0)) := by
  by_cases hb:b=0
  · simp [hb]
  · have h:=scaled_kernel_tendsto ρ hρ hpos hmass hsupport hA hc (neg_ne_zero.mpr hb)
    simpa only [abs_neg,smul_smul,div_eq_mul_inv] using h.const_smul b

theorem complete_quadratic_factor_tendsto (ρ:ℝ→ℝ→ℝ)
    (hρ:∀η,0<η→Integrable (ρ η)) (hpos:∀η,0<η→∀x,0≤ρ η x)
    (hmass:∀η,0<η→∫x,ρ η x=1)
    (hsupport:∀η,0<η→∀x,ρ η x≠0→|x|≤η)
    {A:ℝ→E} (hA:StronglyMeasurable A) (hc:ContinuousAt A 0) (b:ℝ) :
    Tendsto (fun η=>(b^2) • (∫q,ρ η (-b*q) • A q)) (𝓝[>]0) (𝓝 (|b| • A 0)) := by
  by_cases hb:b=0
  · simp [hb]
  · have h:=scaled_kernel_tendsto ρ hρ hpos hmass hsupport hA hc (neg_ne_zero.mpr hb)
    have he:b^2*|b|⁻¹=|b|:=by
      rw [←sq_abs b,pow_two,mul_assoc,mul_inv_cancel₀ (abs_ne_zero.mpr hb),mul_one]
    have ht:=h.const_smul (b^2)
    simp only [abs_neg,smul_smul] at ht
    rw [he] at ht
    exact ht

end
end Resonance.ScaledShrinkingKernel
