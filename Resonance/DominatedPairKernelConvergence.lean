import Resonance.JointEnergyReader
import Mathlib.MeasureTheory.Function.UniformIntegrable

/-! The kernel convergence tool used for an actually marked quartet
pushforward. A positive kernel dominated by one L² kernel becomes small
in L² when its actual total mass tends to zero. -/
open Set MeasureTheory Filter
open scoped ENNReal Topology
namespace Resonance.DominatedPairKernelConvergence
noncomputable section
set_option maxHeartbeats 1800000

theorem dominated_memLp {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f K : α→ℝ} (hK : MemLp K 2 μ) (hf : AEStronglyMeasurable f μ)
    (hb : ∀ᵐx∂μ,0 ≤ f x ∧ f x ≤ K x) : MemLp f 2 μ := by
  apply hK.mono' hf
  filter_upwards [hb] with x hx
  simpa only [Real.norm_eq_abs,abs_of_nonneg hx.1] using hx.2

theorem nonnegative_L1_norm {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f : α→ℝ} (hf : Integrable f μ) (hn : ∀ᵐx∂μ,0 ≤ f x) :
    eLpNorm f 1 μ=ENNReal.ofReal (∫x,f x∂μ) := by
  rw [eLpNorm_one_eq_lintegral_enorm,ofReal_integral_eq_lintegral_ofReal hf hn]
  exact lintegral_congr_ae (hn.mono (fun x hx=>Real.enorm_eq_ofReal hx))

theorem dominated_uniform_integrable {α I : Type*} [MeasurableSpace α]
    {μ : Measure α} {f : I→α→ℝ} {K : α→ℝ} (hK : MemLp K 2 μ)
    (hb : ∀i,∀ᵐx∂μ,0 ≤ f i x ∧ f i x ≤ K x) : UnifIntegrable f 2 μ := by
  intro ε hε
  obtain ⟨δ,hδ,hd⟩:=hK.eLpNorm_indicator_le (by norm_num : (1:ℝ≥0∞)≤2) (by norm_num) hε
  refine ⟨δ,hδ,fun i s hs hμs=>?_⟩
  apply le_trans _ (hd s hs hμs)
  apply eLpNorm_mono_ae
  filter_upwards [hb i] with x hx
  by_cases hxs:x∈s
  · simp only [indicator_of_mem hxs,Real.norm_eq_abs,abs_of_nonneg hx.1,
      abs_of_nonneg (hx.1.trans hx.2)]
    exact hx.2
  · simp only [indicator_of_notMem hxs,norm_zero,le_refl]

/-- The index filter is not forced to be a single selected sequence. -/
theorem actual_mass_to_L2 {α I : Type*} [MeasurableSpace α] {μ : Measure α}
    [IsFiniteMeasure μ] {l : Filter I} [l.IsCountablyGenerated]
    {f : I→α→ℝ} {K : α→ℝ} (hK : MemLp K 2 μ)
    (hf : ∀i,AEStronglyMeasurable (f i) μ)
    (hb : ∀i,∀ᵐx∂μ,0 ≤ f i x ∧ f i x ≤ K x)
    (hsmall : Tendsto (fun i=>∫x,f i x∂μ) l (𝓝 0)) :
    Tendsto (fun i=>eLpNorm (f i) 2 μ) l (𝓝 0) := by
  have hm (i:I):=dominated_memLp hK (hf i) (hb i)
  have hi (i:I) : Integrable (f i) μ:=
    memLp_one_iff_integrable.mp ((hm i).mono_exponent (by norm_num : (1:ℝ≥0∞)≤2))
  have h1 : Tendsto (fun i=>eLpNorm (f i) 1 μ) l (𝓝 0) := by
    simp_rw [nonnegative_L1_norm (hi _) ((hb _).mono (fun _ hx=>hx.1))]
    simpa only [ENNReal.ofReal_zero] using (ENNReal.continuous_ofReal.tendsto 0).comp hsmall
  apply Filter.tendsto_iff_seq_tendsto.mpr
  intro seq hseq
  have hmeasure : TendstoInMeasure μ (fun n=>f (seq n)) atTop (fun _=>0) := by
    apply tendstoInMeasure_of_tendsto_eLpNorm (p:=1) (by norm_num)
      (fun n=>hf (seq n)) aestronglyMeasurable_zero
    simpa only [Pi.sub_apply,Pi.zero_apply,sub_zero,Function.comp_def] using h1.comp hseq
  have hv:=tendsto_Lp_finite_of_tendstoInMeasure (p:=2) (by norm_num) (by norm_num)
    (fun n=>hf (seq n)) (MemLp.zero' : MemLp (fun _:α=>(0:ℝ)) 2 μ)
    (dominated_uniform_integrable hK (fun n=>hb (seq n))) hmeasure
  simpa only [show (fun _:α=>(0:ℝ))=0 from rfl,sub_zero,Function.comp_def] using hv

end
end Resonance.DominatedPairKernelConvergence
