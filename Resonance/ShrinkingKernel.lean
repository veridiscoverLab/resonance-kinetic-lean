import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-! Arbitrary nonnegative unit-mass shrinking kernels. No symmetry, fixed shape,
or height bound occurs in the hypotheses. The integrability used by every
Bochner integral estimate is proved before that estimate. -/
open Set MeasureTheory Filter
open scoped Topology
namespace Resonance.ShrinkingKernel
noncomputable section
variable {E:Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

theorem average_error_bound {ρ:ℝ→ℝ} (hρ:Integrable ρ)
    (hpos:∀x,0≤ρ x) (hmass:∫x,ρ x=1)
    {A:ℝ→E} (hA:AEStronglyMeasurable A) (a:E) {ε:ℝ}
    (hb:∀x,ρ x≠0→‖A x-a‖≤ε) :
    Integrable (fun x=>ρ x • A x) ∧ ‖(∫x,ρ x • A x)-a‖≤ε := by
  have hd:Integrable (fun x=>ρ x • (A x-a)):=by
    apply (hρ.norm.const_mul ε).mono' (hρ.aestronglyMeasurable.smul (hA.sub aestronglyMeasurable_const))
    filter_upwards [] with x
    by_cases hx:ρ x=0
    · simp [hx]
    · rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (hpos x)]
      simpa only [Real.norm_eq_abs,abs_of_nonneg (hpos x),mul_comm] using
        mul_le_mul_of_nonneg_left (hb x hx) (hpos x)
  have hc:Integrable (fun x=>ρ x • a):=hρ.smul_const a
  have hi:Integrable (fun x=>ρ x • A x):=by
    convert hd.add hc using 1
    ext x
    dsimp
    rw [smul_sub,sub_add_cancel]
  refine ⟨hi,?_⟩
  have hid:(∫x,ρ x • A x)-a=∫x,ρ x • (A x-a):=by
    rw [show (fun x=>ρ x • (A x-a))=(fun x=>ρ x • A x)-(fun x=>ρ x • a) from
      funext (fun x=>smul_sub (ρ x) (A x) a)]
    change (∫x,ρ x • A x)-a=∫x,ρ x • A x-ρ x • a
    rw [integral_sub hi hc,
      integral_smul_const,hmass,one_smul]
  rw [hid]
  calc
    _ ≤ ∫x,‖ρ x • (A x-a)‖:=norm_integral_le_integral_norm _
    _ ≤ ∫x,ε*ρ x:=by
      apply integral_mono_ae hd.norm (hρ.const_mul ε)
      filter_upwards [] with x
      by_cases hx:ρ x=0
      · simp [hx]
      · rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (hpos x)]
        simpa only [mul_comm] using mul_le_mul_of_nonneg_left (hb x hx) (hpos x)
    _ = ε:=by rw [integral_const_mul,hmass,mul_one]

theorem arbitrary_kernel_tendsto (ρ:ℝ→ℝ→ℝ)
    (hρ:∀η,0<η→Integrable (ρ η)) (hpos:∀η,0<η→∀x,0≤ρ η x)
    (hmass:∀η,0<η→∫x,ρ η x=1)
    (hsupport:∀η,0<η→∀x,ρ η x≠0→|x|≤η)
    {A:ℝ→E} (hA:AEStronglyMeasurable A) (hc:ContinuousAt A 0) :
    Tendsto (fun η=>∫x,ρ η x • A x) (𝓝[>]0) (𝓝 (A 0)) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨δ,hδ,hclose⟩:=Metric.continuousAt_iff.mp hc (ε/2) (by positivity)
  have hnear:∀ᶠη:ℝ in 𝓝[>]0,0<η∧η<δ:=by
    filter_upwards [self_mem_nhdsWithin,(eventually_lt_nhds hδ).filter_mono nhdsWithin_le_nhds]
      with η hη hηδ
    exact ⟨hη,hηδ⟩
  filter_upwards [hnear] with η hη
  have hb:∀x,ρ η x≠0→‖A x-A 0‖≤ε/2:=by
    intro x hx
    have hxδ:dist x 0<δ:=by
      rw [Real.dist_eq,sub_zero]
      exact (hsupport η hη.1 x hx).trans_lt hη.2
    simpa only [dist_eq_norm] using (hclose hxδ).le
  rw [dist_eq_norm]
  exact (average_error_bound (hρ η hη.1) (hpos η hη.1) (hmass η hη.1) hA (A 0)
    hb).2.trans_lt (by linarith)

end
end Resonance.ShrinkingKernel
