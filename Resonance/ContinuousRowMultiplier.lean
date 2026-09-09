import Resonance.ContinuousRowOperator
import Mathlib.Analysis.Normed.Operator.Mul

/-! A bounded measurable input multiplier need not act on C(Y).
It acts inside each original integral row.  This is the mechanism needed
for the actual ratio of two vanishing corner frequencies. -/
open MeasureTheory Set Filter
open scoped Topology
namespace Resonance.ContinuousRowMultiplier
noncomputable section
set_option maxHeartbeats 800000
variable {X Y : Type*} [TopologicalSpace X] [CompactSpace X]
  [TopologicalSpace Y] [CompactSpace Y] [MeasurableSpace Y] [BorelSpace Y]
  {μ : Measure Y}

omit [TopologicalSpace X] [CompactSpace X] [TopologicalSpace Y] [CompactSpace Y] [BorelSpace Y] in
theorem mul_rows_integrable (K : X → Y → ℝ) (hi : ∀ x, Integrable (K x) μ)
    (b : Y → ℝ) (hbm : AEStronglyMeasurable b μ) {B : ℝ}
    (hb : ∀ᵐ y ∂μ, ‖b y‖ ≤ B) (x : X) :
    Integrable (fun y => K x y*b y) μ := (hi x).mul_bdd hbm hb

omit [CompactSpace X] [TopologicalSpace Y] [CompactSpace Y] [BorelSpace Y] in
theorem mul_rows_L1_continuous (K : X → Y → ℝ) (hi : ∀ x, Integrable (K x) μ)
    (hc : ∀ x, Tendsto (fun a => ∫ y, ‖K a y-K x y‖ ∂μ) (𝓝 x) (𝓝 0))
    (b : Y → ℝ) (hbm : AEStronglyMeasurable b μ) {B : ℝ} (_hB : 0 ≤ B)
    (hb : ∀ᵐ y ∂μ, ‖b y‖ ≤ B) (x : X) :
    Tendsto (fun a => ∫ y, ‖K a y*b y-K x y*b y‖ ∂μ) (𝓝 x) (𝓝 0) := by
  have hbound (a : X) : (∫ y, ‖K a y*b y-K x y*b y‖ ∂μ) ≤
      B*(∫ y, ‖K a y-K x y‖ ∂μ) := by
    rw [← integral_const_mul]
    apply integral_mono_ae
      ((mul_rows_integrable K hi b hbm hb a).sub
        (mul_rows_integrable K hi b hbm hb x)).norm
      (((hi a).sub (hi x)).norm.const_mul B)
    filter_upwards [hb] with y hy
    change ‖K a y*b y-K x y*b y‖ ≤ B*‖K a y-K x y‖
    rw [← sub_mul,norm_mul]
    exact (mul_le_mul_of_nonneg_left hy (norm_nonneg _)).trans_eq (mul_comm _ _)
  apply squeeze_zero (fun _ => integral_nonneg (fun _ => norm_nonneg _)) hbound
  simpa only [mul_zero] using (tendsto_const_nhds (x := B)).mul (hc x)

theorem exists_compact_mul_operator (K : X → Y → ℝ) (hi : ∀ x, Integrable (K x) μ)
    (hc : ∀ x, Tendsto (fun a => ∫ y, ‖K a y-K x y‖ ∂μ) (𝓝 x) (𝓝 0))
    (b : Y → ℝ) (hbm : AEStronglyMeasurable b μ) {B : ℝ} (hB : 0 ≤ B)
    (hb : ∀ᵐ y ∂μ, ‖b y‖ ≤ B) (a : C(X,ℝ)) :
    ∃ T : C(Y,ℝ) →L[ℝ] C(X,ℝ), IsCompactOperator T ∧
      ∀ f x, T f x = a x*(∫ y, (K x y*b y)*f y ∂μ) := by
  obtain ⟨T,hT,hread⟩ := ContinuousRowOperator.exists_compact_operator
    (fun x y => K x y*b y) (mul_rows_integrable K hi b hbm hb)
    (mul_rows_L1_continuous K hi hc b hbm hB hb)
  let M := ContinuousLinearMap.mul ℝ C(X,ℝ) a
  refine ⟨M.comp T,hT.clm_comp M,?_⟩
  intro f x
  change a x*T f x=_
  rw [hread]

end
end Resonance.ContinuousRowMultiplier
