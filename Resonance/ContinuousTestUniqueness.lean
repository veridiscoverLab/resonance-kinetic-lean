import Mathlib.MeasureTheory.Function.AEEqOfIntegral
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.Complex.Basic

/-! Continuous tests determine an actual L¹ density on a compact metric
space. The compact-set indicators are approximated explicitly, not assumed
to lie in a smooth or form domain. -/
open Set MeasureTheory Filter Metric
open scoped Topology
namespace Resonance.ContinuousTestUniqueness
noncomputable section
variable {Y : Type*} [MetricSpace Y]

def cutoff (S : Set Y) (n : ℕ) (y : Y) : ℝ := max 0 (1-(n:ℝ)*infDist y S)

theorem cutoff_continuous (S : Set Y) (n : ℕ) : Continuous (cutoff S n) :=
  continuous_const.max (continuous_const.sub (continuous_const.mul (continuous_infDist_pt S)))

theorem cutoff_bounds (S : Set Y) (n : ℕ) (y : Y) :
    0≤cutoff S n y ∧ cutoff S n y≤1 := by
  constructor
  · exact le_max_left _ _
  · apply max_le (by norm_num)
    have h := mul_nonneg (Nat.cast_nonneg n) (infDist_nonneg (x:=y) (s:=S))
    linarith

theorem cutoff_tendsto {S : Set Y} (hS : IsClosed S) (hS0 : S.Nonempty) (y : Y) :
    Tendsto (fun n=>cutoff S n y) atTop (𝓝 (S.indicator (fun _=>(1:ℝ)) y)) := by
  by_cases hy:y∈S
  · simpa only [cutoff,infDist_zero_of_mem hy,mul_zero,sub_zero,max_eq_right (by norm_num : (0:ℝ)≤1),
      indicator_of_mem hy] using (tendsto_const_nhds (x:=(1:ℝ)))
  · have hd := (hS.notMem_iff_infDist_pos hS0).mp hy
    obtain ⟨N,hN⟩ := exists_nat_gt (1/infDist y S)
    have hzero : ∀ᶠn:ℕ in atTop,cutoff S n y=0 := by
      filter_upwards [eventually_ge_atTop N] with n hn
      have hlt : 1/infDist y S<(n:ℝ) := hN.trans_le (by exact_mod_cast hn)
      have hmul := (div_lt_iff₀ hd).mp hlt
      exact max_eq_left (by linarith)
    rw [indicator_of_notMem hy]
    exact tendsto_const_nhds.congr' (hzero.mono (fun _ hn=>hn.symm))

variable [CompactSpace Y] [MeasurableSpace Y] [BorelSpace Y]

theorem ae_zero_of_continuous_tests (μ : Measure Y) {f : Y→ℂ} (hf : Integrable f μ)
    (h : ∀ψ:C(Y,ℂ),(∫y,ψ y*f y ∂μ)=0) : f=ᵐ[μ] 0 := by
  apply ae_eq_zero_of_forall_setIntegral_isCompact_eq_zero hf
  intro S hS
  rcases S.eq_empty_or_nonempty with hE|hS0
  · simp [hE]
  let ψ : ℕ→C(Y,ℂ) := fun n=>⟨fun y=>(cutoff S n y:ℂ),
    Complex.continuous_ofReal.comp (cutoff_continuous S n)⟩
  have hmeas : ∀n,AEStronglyMeasurable (fun y=>ψ n y*f y) μ :=
    fun n=>(ψ n).continuous.aestronglyMeasurable.mul hf.aestronglyMeasurable
  have hbound : ∀n,∀ᵐy∂μ,‖ψ n y*f y‖≤‖f y‖ := by
    intro n
    exact Eventually.of_forall (fun y=>by
      rw [norm_mul]
      have hh : ‖ψ n y‖≤1 := by
        simpa only [ψ,ContinuousMap.coe_mk,Complex.norm_real,Real.norm_eq_abs,
          abs_of_nonneg (cutoff_bounds S n y).1] using (cutoff_bounds S n y).2
      exact (mul_le_mul_of_nonneg_right hh (norm_nonneg _)).trans_eq (one_mul _))
  have ht := tendsto_integral_of_dominated_convergence (fun y=>‖f y‖) hmeas hf.norm hbound
    (Eventually.of_forall (fun y=>
      (Complex.continuous_ofReal.continuousAt.tendsto.comp (cutoff_tendsto hS.isClosed hS0 y)).mul
        (tendsto_const_nhds (x:=f y))))
  have hz : Tendsto (fun n=>∫y,ψ n y*f y ∂μ) atTop (𝓝 (0:ℂ)) := by
    simpa only [h] using (tendsto_const_nhds (x:=(0:ℂ)))
  have he := tendsto_nhds_unique ht hz
  have hfun : (fun y=>Complex.ofReal (S.indicator (fun _=>(1:ℝ)) y)*f y)=S.indicator f := by
    funext y
    by_cases hy:y∈S <;> simp [hy]
  calc
    _ = ∫y,S.indicator f y ∂μ := (integral_indicator hS.measurableSet).symm
    _ = ∫y,Complex.ofReal (S.indicator (fun _=>(1:ℝ)) y)*f y ∂μ :=
      integral_congr_ae (Eventually.of_forall (fun y=>congrFun hfun.symm y))
    _ = 0 := he

end
end Resonance.ContinuousTestUniqueness
