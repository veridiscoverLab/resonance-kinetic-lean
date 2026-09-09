import Resonance.PinnedCriticalGauge
import Resonance.CriticalSourceCutoff
import Resonance.PinnedUniformCancellation
import Resonance.PinnedMeasureNormalization

/-! Removal of the shared-factor cutoff for the original complete four-leg
source in its original Euclidean coarea. Its L1 budget is proved, not assumed. -/
open Set MeasureTheory Filter
open scoped Topology
namespace Resonance.PinnedCompleteSourceCutoff
noncomputable section
open PinnedMeasure PinnedPeriodicity PinnedCriticalGauge
open PinnedCriticalCancellation PinnedUniformCancellation PinnedMeasureNormalization

def sharedProduct (swap : Bool) (n m : ℤ) (k : Ambient) : ℝ :=
  (gaugeHomeomorph swap n m).symm k 1 * (gaugeHomeomorph swap n m).symm k 2

theorem sharedProduct_continuous (swap : Bool) (n m : ℤ) :
    Continuous (sharedProduct swap n m) := by
  unfold sharedProduct
  exact ((PiLp.continuous_apply 2 (fun _ : Fin 3=>ℝ) 1).comp
    (gaugeHomeomorph swap n m).symm.continuous).mul
      ((PiLp.continuous_apply 2 (fun _ : Fin 3=>ℝ) 2).comp
        (gaugeHomeomorph swap n m).symm.continuous)

theorem difference_zero_on_shared_zero {φ : ℝ → ℂ} (hφ : ContDiff ℝ 2 φ)
    (hp : Function.Periodic φ period) (swap : Bool) (n m : ℤ) (k : Ambient)
    (hb : sharedProduct swap n m k=0) : fullDifference φ k=0 := by
  let p := (gaugeHomeomorph swap n m).symm k
  have hk : gaugeHomeomorph swap n m p=k := (gaugeHomeomorph swap n m).apply_symm_apply k
  rw [←hk,gauge_difference hp,complex_rectangle_factor hφ]
  have hh : p 1*p 2=0 := hb
  rw [neg_mul, hh]
  simp

theorem complete_source_integrable {d : ℝ} (hd0 : 0<d) (hdU : d<1/2)
    {φ : ℝ → ℂ} (hφ : ContDiff ℝ 2 φ) (hp : Function.Periodic φ period)
    {W : Ambient → ℂ} (hW : Continuous W) (hK : HasCompactSupport W) :
    Integrable (fun k=>W k*fullDifference φ k) (euclideanLiftedRegularCoarea d) := by
  have hi : IntegrableOn (fun k=>‖fullDifference φ k‖) (tsupport W)
      (euclideanLiftedRegularCoarea d) := by
    unfold IntegrableOn
    rw [euclideanLiftedRegularCoarea_eq_smul,Measure.restrict_smul]
    exact (full_difference_integrableOn hd0 hdU hφ hp hK).smul_measure ENNReal.coe_ne_top
  obtain ⟨C,hC⟩ := hK.exists_bound_of_continuous hW
  have hsrc : IntegrableOn (fun k=>W k*fullDifference φ k) (tsupport W)
      (euclideanLiftedRegularCoarea d) := by
    apply (hi.const_mul C).mono' (hW.mul (fullDifference_continuous hφ.continuous)).aestronglyMeasurable
    filter_upwards [] with k
    simp only [Pi.mul_apply]
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (hC k) (norm_nonneg _)
  apply hsrc.integrable_of_forall_notMem_eq_zero
  intro k hk
  have hz : W k=0 := by by_contra hn; exact hk (subset_tsupport W hn)
  rw [hz,zero_mul]

theorem original_cutoff_tendsto {d : ℝ} (hd0 : 0<d) (hdU : d<1/2)
    {φ : ℝ → ℂ} (hφ : ContDiff ℝ 2 φ) (hp : Function.Periodic φ period)
    {W : Ambient → ℂ} (hW : Continuous W) (hK : HasCompactSupport W)
    (swap : Bool) (n m : ℤ) :
    Tendsto (fun δ=>∫k,CriticalSourceCutoff.cutoff δ (sharedProduct swap n m k) •
      (W k*fullDifference φ k) ∂euclideanLiftedRegularCoarea d) (𝓝[>]0)
      (𝓝 (∫k,W k*fullDifference φ k ∂euclideanLiftedRegularCoarea d)) := by
  apply CriticalSourceCutoff.integral_tendsto (sharedProduct_continuous swap n m).measurable
    (complete_source_integrable hd0 hdU hφ hp hW hK)
  filter_upwards [] with k hk
  rw [difference_zero_on_shared_zero hφ hp swap n m k hk,mul_zero]

end
end Resonance.PinnedCompleteSourceCutoff
