import Resonance.PinnedFiniteAverages
import Resonance.FiniteCoverEnergy

/-! Near-kernel compactness is derived from the original finite actual
averages and their full-coarea defect estimate.  In particular no marginal
boundedness for the full coarea and no finite total coarea mass is assumed. -/
open Real MeasureTheory Set Filter
open scoped ENNReal NNReal Topology ContDiff BoundedContinuousFunction
namespace Resonance.PinnedNearKernelCompactness
noncomputable section
set_option maxHeartbeats 1000000
open Resonance.PinnedPeriodicity Resonance.PinnedClassificationFinal
open Resonance.PinnedFiniteAverages

theorem enorm_three_sum_sq_le (u v w:ℂ) :
    ‖u+v+w‖ₑ^2≤3*(‖u‖ₑ^2+‖v‖ₑ^2+‖w‖ₑ^2) := by
  have hn : ‖u+v+w‖≤‖u‖+‖v‖+‖w‖ :=
    (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
  have hr : ‖u+v+w‖^2≤3*(‖u‖^2+‖v‖^2+‖w‖^2) := by
    have h0 := norm_nonneg (u+v+w)
    have hu := norm_nonneg u
    have hv := norm_nonneg v
    have hw := norm_nonneg w
    nlinarith [sq_nonneg (‖u‖-‖v‖),sq_nonneg (‖u‖-‖w‖),sq_nonneg (‖v‖-‖w‖)]
  have he := ENNReal.ofReal_le_ofReal hr
  rw [ENNReal.ofReal_mul (by norm_num : (0:ℝ)≤3),
    ENNReal.ofReal_add (add_nonneg (sq_nonneg ‖u‖) (sq_nonneg ‖v‖)) (sq_nonneg ‖w‖),
    ENNReal.ofReal_add (sq_nonneg ‖u‖) (sq_nonneg ‖v‖)] at he
  simpa only [ENNReal.ofReal_pow (norm_nonneg _),ofReal_norm,ENNReal.ofReal_ofNat] using he

theorem bounded_average_pair_energy_tendsto
    {X:Type*} [MeasurableSpace X] [TopologicalSpace X]
    {μ:Measure X} {S:Set X} (hS:MeasurableSet S) (hfinite:μ S≠⊤)
    {F:ℕ→X→ℂ} {A:ℕ→S→ᵇℂ} {g:S→ᵇℂ}
    (hA:∀(n:ℕ) (x:S),A n x=F n x) (hconv:Tendsto A atTop (𝓝 g)) :
    Tendsto (fun p:ℕ×ℕ=>∫⁻x in S,‖F p.1 x-F p.2 x‖ₑ^2 ∂μ)
      (atTop×ˢatTop) (𝓝 0) := by
  have hn : Tendsto (fun p:ℕ×ℕ=>‖A p.1-A p.2‖ₑ) (atTop×ˢatTop) (𝓝 0) := by
    simpa only [sub_self,enorm_zero] using
      ((hconv.comp tendsto_fst).sub (hconv.comp tendsto_snd)).enorm
  have hdiff : Tendsto (fun p:ℕ×ℕ=>‖A p.1-A p.2‖ₑ^2) (atTop×ˢatTop) (𝓝 0) := by
    simpa [Function.comp_def,ENNReal.rpow_natCast] using
      (ENNReal.continuous_rpow_const (y:=2)).continuousAt.tendsto.comp hn
  have hlim : Tendsto (fun p:ℕ×ℕ=>‖A p.1-A p.2‖ₑ^2*μ S)
      (atTop×ˢatTop) (𝓝 0) := by
    simpa only [zero_mul] using ENNReal.Tendsto.mul_const hdiff (Or.inr hfinite)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
    (fun _=>zero_le _) (fun p=>?_)
  calc
    _ ≤ ∫⁻_x in S,‖A p.1-A p.2‖ₑ^2 ∂μ := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem hS] with x hx
      have hb := ENNReal.ofReal_le_ofReal ((A p.1-A p.2).norm_coe_le_norm ⟨x,hx⟩)
      have he : ‖F p.1 x-F p.2 x‖ₑ≤‖A p.1-A p.2‖ₑ := by
        simpa only [ofReal_norm,BoundedContinuousFunction.coe_sub,Pi.sub_apply,hA] using hb
      exact pow_le_pow_left' he 2
    _ = _ := by simp

theorem pair_error_energy_le {X:Type*} [MeasurableSpace X] {μ:Measure X}
    {f g A B:X→ℂ} (hf:AEStronglyMeasurable f μ) (_hg:AEStronglyMeasurable g μ)
    (hA:AEStronglyMeasurable A μ) (hB:AEStronglyMeasurable B μ) :
    (∫⁻x,‖f x-g x‖ₑ^2 ∂μ) ≤ 3*((∫⁻x,‖f x-A x‖ₑ^2 ∂μ)+
      (∫⁻x,‖A x-B x‖ₑ^2 ∂μ)+(∫⁻x,‖g x-B x‖ₑ^2 ∂μ)) := by
  have hpoint (x:X) : ‖f x-g x‖ₑ^2 ≤
      3*(‖f x-A x‖ₑ^2+‖A x-B x‖ₑ^2+‖g x-B x‖ₑ^2) := by
    have he := enorm_three_sum_sq_le (f x-A x) (A x-B x) (B x-g x)
    rw [show f x-A x+(A x-B x)+(B x-g x)=f x-g x by ring,
      enorm_sub_rev (B x) (g x)] at he
    exact he
  apply (lintegral_mono hpoint).trans_eq
  rw [lintegral_const_mul' _ _ (by norm_num)]
  have he₀ : AEMeasurable (fun x=>‖f x-A x‖ₑ^2) μ := (hf.sub hA).enorm.pow_const 2
  have he₁ : AEMeasurable (fun x=>‖A x-B x‖ₑ^2) μ := (hA.sub hB).enorm.pow_const 2
  rw [lintegral_add_left' (he₀.add he₁),lintegral_add_left' he₀]

/-- A locally small full-difference defect plus the compact complete
average forces the original sequence to be Cauchy on that same target. -/
theorem local_pair_energy_tendsto {d:ℝ} (C:AverageChart d)
    {φ:ℕ→PinnedPeriodicity.Circle→ℂ} (hφ:∀n,MemLp (φ n) 2 circleHaar)
    (hm:∀n,Measurable (φ n))
    {g:C.target→ᵇℂ}
    (hconv:TendstoUniformly (fun n (x:C.target)=>C.value (φ n) x) g atTop)
    (herr:Tendsto (fun n=>∫⁻x in C.target,‖periodicLift (φ n) x-C.value (φ n) x‖ₑ^2)
      atTop (𝓝 0)) :
    Tendsto (fun p:ℕ×ℕ=>∫⁻x in C.target,
      ‖periodicLift (φ p.1) x-periodicLift (φ p.2) x‖ₑ^2)
      (atTop×ˢatTop) (𝓝 0) := by
  have hconvA : Tendsto (fun n=>C.asBounded (φ n) (hφ n)) atTop (𝓝 g) := by
    apply BoundedContinuousFunction.tendsto_iff_tendstoUniformly.mpr
    simpa only [AverageChart.asBounded_apply] using hconv
  have havg : Tendsto (fun p:ℕ×ℕ=>∫⁻x in C.target,
      ‖C.value (φ p.1) x-C.value (φ p.2) x‖ₑ^2) (atTop×ˢatTop) (𝓝 0) :=
    bounded_average_pair_energy_tendsto (μ:=volume) (F:=fun n=>C.value (φ n))
      C.target_compact.measurableSet
      (C.target_compact.measure_lt_top).ne
      (A:=fun n=>C.asBounded (φ n) (hφ n))
      (fun n x=>C.asBounded_apply (φ n) (hφ n) x) hconvA
  have hlim := ENNReal.Tendsto.const_mul
    (((herr.comp tendsto_fst).add havg).add (herr.comp tendsto_snd))
    (a:=3) (Or.inr (by norm_num : (3:ℝ≥0∞)≠⊤))
  simp only [add_zero,mul_zero] at hlim
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
    (fun _=>zero_le _) (fun p=>?_)
  have hf (n:ℕ) : AEStronglyMeasurable (periodicLift (φ n))
      (volume.restrict C.target) :=
    ((hm n).comp (AddCircle.continuous_mk' period).measurable).aestronglyMeasurable
  have hA (n:ℕ) : AEStronglyMeasurable (C.value (φ n))
      (volume.restrict C.target) := by
    obtain ⟨_B₀,_B₁,_hB₀,_hB₁,hall⟩ := C.uniform_C1
    have hc : ContinuousOn (C.value (φ n)) C.target :=
      fun x hx=>(hall (φ n) (hφ n) x hx).1.continuousAt.continuousWithinAt
    exact hc.aestronglyMeasurable C.target_compact.measurableSet
  exact pair_error_energy_le (hf p.1) (hf p.2) (hA p.1) (hA p.2)

/-- Every bounded sequence whose original complete coarea difference
vanishes has a subsequence Cauchy in the full fundamental-interval L²
energy.  Every local chart and every source average is derived above. -/
theorem actual_near_kernel_subsequence_energy {d:ℝ} (hd0:0<d) (hdU:d<1/2)
    {φ:ℕ→PinnedPeriodicity.Circle→ℂ} (hm:∀n,Measurable (φ n))
    (hφ:∀n,MemLp (φ n) 2 circleHaar)
    {R:ℝ≥0∞} (hR:R≠⊤) (hbound:∀n,eLpNorm (φ n) 2 circleHaar≤R)
    (henergy:Tendsto (fun n=>∫⁻k,‖PinnedMaximalDifference.difference (φ n) k‖ₑ^2
      ∂circleRegularCoarea d) atTop (𝓝 0)) :
    ∃s:ℕ→ℕ,StrictMono s ∧ Tendsto (fun p:ℕ×ℕ=>∫⁻x in Icc 0 period,
      ‖periodicLift (φ (s p.1)) x-periodicLift (φ (s p.2)) x‖ₑ^2)
      (atTop×ˢatTop) (𝓝 0) := by
  classical
  obtain ⟨J,C,hcover⟩ := finite_actual_chart_cover hd0 hdU
  obtain ⟨g,s,hs,havg⟩ := finite_average_common_subsequence
    (fun i:(J:Set ℝ)=>C i) hφ hR hbound
  refine ⟨s,hs,?_⟩
  have hcover' : Icc 0 period ⊆ ⋃i:(J:Set ℝ),(C i).target := by
    intro x hx
    obtain ⟨j,hj,hxj⟩ := hcover x hx
    exact mem_iUnion.mpr ⟨⟨j,hj⟩,hxj⟩
  apply FiniteCoverEnergy.tendsto_zero_of_finite_cover volume (Icc 0 period)
    (fun i:(J:Set ℝ)=>(C i).target) hcover' (atTop×ˢatTop)
    (fun p:ℕ×ℕ=>fun x=>‖periodicLift (φ (s p.1)) x-periodicLift (φ (s p.2)) x‖ₑ^2)
  intro i
  apply local_pair_energy_tendsto (C i) (fun n=>hφ (s n)) (fun n=>hm (s n)) (havg i)
  obtain ⟨B,hB,hlocal⟩ := (C i).energy_le hd0 hdU
  have hlim := ENNReal.Tendsto.const_mul (henergy.comp hs.tendsto_atTop)
    (a:=B) (Or.inr hB)
  simp only [mul_zero] at hlim
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
    (fun _=>zero_le _) (fun n=>hlocal (φ (s n)) (hm (s n)) (hφ (s n)))

end
end Resonance.PinnedNearKernelCompactness
