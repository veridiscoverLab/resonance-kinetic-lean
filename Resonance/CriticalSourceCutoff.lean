import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Topology.Algebra.Support
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! A continuous cutoff of the shared vanishing factor. Its removal uses the
original integrable complete source, which is zero on the factor-zero set. -/
open Set MeasureTheory Filter
open scoped Topology
namespace Resonance.CriticalSourceCutoff
noncomputable section

def cutoff (δ t : ℝ) : ℝ := max 0 (min 1 ((|t|-δ)/δ))

theorem cutoff_continuous (δ : ℝ) : Continuous (cutoff δ) := by unfold cutoff; fun_prop

theorem cutoff_bounds (δ t : ℝ) : 0≤cutoff δ t ∧ cutoff δ t≤1 := by
  constructor
  · exact le_max_left _ _
  · exact max_le (by norm_num) (min_le_left _ _)

theorem cutoff_zero {δ t : ℝ} (hδ : 0<δ) (ht : |t|≤δ) : cutoff δ t=0 := by
  unfold cutoff
  apply max_eq_left
  exact (min_le_right _ _).trans (div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr ht) hδ.le)

theorem cutoff_one {δ t : ℝ} (hδ : 0<δ) (ht : 2*δ≤|t|) : cutoff δ t=1 := by
  have hh : 1≤(|t|-δ)/δ := (le_div_iff₀ hδ).mpr (by linarith)
  simp only [cutoff,min_eq_left hh,max_eq_right (by norm_num : (0:ℝ)≤1)]

theorem cutoff_tendsto {t : ℝ} (ht : t≠0) :
    Tendsto (fun δ=>cutoff δ t) (𝓝[>]0) (𝓝 1) := by
  apply tendsto_const_nhds.congr'
  have ha : 0 < |t|/2 := half_pos (abs_pos.mpr ht)
  filter_upwards [self_mem_nhdsWithin,
    (eventually_lt_nhds ha).filter_mono nhdsWithin_le_nhds] with δ hδ hsmall
  exact (cutoff_one hδ (by linarith)).symm

theorem cutoff_support {X : Type*} [TopologicalSpace X] {b : X → ℝ}
    (hb : Continuous b) {δ : ℝ} (hδ : 0<δ) :
    tsupport (fun x=>cutoff δ (b x))⊆{x|δ≤|b x|} := by
  apply closure_minimal
  · intro x hx
    by_contra hn
    exact hx (cutoff_zero hδ (le_of_lt (lt_of_not_ge hn)))
  · exact isClosed_le continuous_const hb.abs

theorem source_integrable {X E : Type*} [MeasurableSpace X]
    [NormedAddCommGroup E] [NormedSpace ℝ E] {μ : Measure X}
    {b : X → ℝ} (hb : Measurable b) {B : X → E} (hB : Integrable B μ) (δ : ℝ) :
    Integrable (fun x=>cutoff δ (b x) • B x) μ := by
  apply hB.norm.mono' (((cutoff_continuous δ).measurable.comp hb).aestronglyMeasurable.smul hB.aestronglyMeasurable)
  filter_upwards [] with x
  simp only [Function.comp_apply]
  rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (cutoff_bounds δ (b x)).1]
  exact (mul_le_mul_of_nonneg_right (cutoff_bounds δ (b x)).2 (norm_nonneg _)).trans_eq (one_mul _)

theorem integral_tendsto {X E : Type*} [MeasurableSpace X]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] {μ : Measure X}
    {b : X → ℝ} (hb : Measurable b) {B : X → E} (hB : Integrable B μ)
    (hz : ∀ᵐx ∂μ,b x=0→B x=0) :
    Tendsto (fun δ=>∫x,cutoff δ (b x) • B x ∂μ) (𝓝[>]0) (𝓝 (∫x,B x ∂μ)) := by
  apply tendsto_integral_filter_of_dominated_convergence (fun x=>‖B x‖)
  · exact Filter.Eventually.of_forall (fun δ=>(source_integrable hb hB δ).aestronglyMeasurable)
  · exact Filter.Eventually.of_forall (fun δ=>ae_of_all μ (fun x=>by
      rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (cutoff_bounds δ (b x)).1]
      exact (mul_le_mul_of_nonneg_right (cutoff_bounds δ (b x)).2 (norm_nonneg _)).trans_eq (one_mul _)))
  · exact hB.norm
  · filter_upwards [hz] with x hx
    by_cases hbx : b x=0
    · simp [hx hbx]
    · simpa only [one_smul] using (cutoff_tendsto hbx).smul_const (B x)

end
end Resonance.CriticalSourceCutoff
