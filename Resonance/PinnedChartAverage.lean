import Resonance.PinnedPeriodicSourceBounds
import Resonance.PinnedAverageCompactness

/-! The averaging operator below acts on a single original circle function.
All source Jacobians and compact source supports are derived from the genuine
chart; its source norms are controlled by that function's probability-Haar
L² norm. -/
open Real MeasureTheory Set Filter
open scoped ENNReal NNReal Topology ContDiff BoundedContinuousFunction
namespace Resonance.PinnedChartAverage
noncomputable section
open Resonance.PinnedSmoothing Resonance.PinnedLocalSmooth
open Resonance.PinnedPeriodicity Resonance.PinnedClassificationFinal

def legAverage (H : ℝ×ℝ→ℝ) (ρ : ℝ→ℝ) (z r : ℝ)
    (φ : PinnedPeriodicity.Circle→ℂ) (a : ℝ) : ℂ :=
  ∫ t in Icc (z-r/4) (z+r/4), ρ t • periodicLift φ (H (a,t))

theorem bump_average_L2_uniform_C1 {H : ℝ×ℝ→ℝ} {x z r κ : ℝ}
    (hr : 0<r) (hκ : 0<κ)
    (hs : ContDiffOn ℝ ∞ H (Metric.ball x r ×ˢ Metric.ball z r))
    (hb : ∀ p∈Metric.ball x r ×ˢ Metric.ball z r, κ≤|partialZ H p|)
    {ρ : ℝ→ℝ} (hρ : ContDiff ℝ ∞ ρ)
    (hρsupp : tsupport ρ ⊆ Metric.ball z (r/8)) :
    ∃ C₀ C₁ : ℝ≥0∞, C₀≠⊤ ∧ C₁≠⊤ ∧
      ∀ φ : PinnedPeriodicity.Circle→ℂ, MemLp φ 2 circleHaar →
      ∀ a∈Metric.ball x (r/4),
        DifferentiableAt ℝ (legAverage H ρ z r φ) a ∧
        ‖legAverage H ρ z r φ a‖ₑ ≤ C₀*eLpNorm φ 2 circleHaar ∧
        ‖deriv (legAverage H ρ z r φ) a‖ₑ ≤ C₁*eLpNorm φ 2 circleHaar := by
  obtain ⟨L,hL,hdata⟩ := compact_chart_source_data hr hκ hs hb
  obtain ⟨C,hC,hsource⟩ := PinnedPeriodicSourceBounds.circle_L2_local_source_bound
    (by linarith : -L≤L)
  have hsub : Icc (z-r/4) (z+r/4) ⊆ Metric.ball z (r/2) := by
    rw [← Real.closedBall_eq_Icc]
    exact Metric.closedBall_subset_ball (by linarith)
  have ha : z-r/4 ∉ tsupport ρ := by
    intro h
    have hh := hρsupp h
    rw [Metric.mem_ball,Real.dist_eq,show z-r/4-z=-(r/4) by ring,
      abs_neg,abs_of_pos (by positivity)] at hh
    linarith
  have hb' : z+r/4 ∉ tsupport ρ := by
    intro h
    have hh := hρsupp h
    rw [Metric.mem_ball,Real.dist_eq,show z+r/4-z=r/4 by ring,
      abs_of_pos (by positivity)] at hh
    linarith
  have hhalf : Metric.ball x (r/2) ×ˢ Metric.ball z (r/2) ⊆
      Metric.ball x r ×ˢ Metric.ball z r :=
    Set.prod_mono (Metric.ball_subset_ball (by linarith))
      (Metric.ball_subset_ball (by linarith))
  obtain ⟨C₀,C₁,hC₀,hC₁,hall⟩ := PinnedAverageBounds.actual_L1_average_uniform_C1
    Metric.isOpen_ball Metric.isOpen_ball Metric.isOpen_ball
    (isCompact_closedBall x (r/4)) Metric.ball_subset_closedBall
    (Metric.closedBall_subset_ball (by linarith))
    (by linarith : z-r/4≤z+r/4) hsub (hs.mono hhalf)
    (hρ.comp contDiff_snd).contDiffOn
    (fun p hp => abs_pos.mp (lt_of_lt_of_le hκ (hb p (hhalf hp))))
    (fun _ _ => by
      change ρ (z-r/4)=0 ∧ ρ (z+r/4)=0
      exact ⟨image_eq_zero_of_notMem_tsupport ha,
        image_eq_zero_of_notMem_tsupport hb'⟩)
    (ENNReal.inv_ne_top.mpr (ne_of_gt (ENNReal.ofReal_pos.mpr hκ)))
    (fun a ha => (hdata a ha).1) (fun a ha => (hdata a ha).2)
  refine ⟨C₀*C,C₁*C,ENNReal.mul_ne_top hC₀ hC,
    ENNReal.mul_ne_top hC₁ hC,?_⟩
  intro φ hφ a ha
  obtain ⟨hi,hle⟩ := hsource φ hφ
  have hh := hall (periodicLift φ) hi a ha
  refine ⟨hh.1.differentiableAt,?_,?_⟩
  · exact hh.2.1.trans (by simpa only [mul_assoc] using mul_le_mul_right hle C₀)
  · exact hh.2.2.trans (by simpa only [mul_assoc] using mul_le_mul_right hle C₁)

/-- A real resonance chart's source average is compact on every smaller
closed target interval, for a bounded sequence in the original circle L². -/
theorem bump_average_L2_subsequence {H : ℝ×ℝ→ℝ} {x z r κ l u : ℝ}
    (hr : 0<r) (hκ : 0<κ)
    (hs : ContDiffOn ℝ ∞ H (Metric.ball x r ×ˢ Metric.ball z r))
    (hb : ∀ p∈Metric.ball x r ×ˢ Metric.ball z r, κ≤|partialZ H p|)
    {ρ : ℝ→ℝ} (hρ : ContDiff ℝ ∞ ρ)
    (hρsupp : tsupport ρ ⊆ Metric.ball z (r/8))
    (hlu : Icc l u ⊆ Metric.ball x (r/4))
    {φ : ℕ→PinnedPeriodicity.Circle→ℂ} (hφ : ∀n,MemLp (φ n) 2 circleHaar)
    {R : ℝ≥0∞} (hR : R≠⊤) (hbound : ∀n,eLpNorm (φ n) 2 circleHaar≤R) :
    ∃g:(Icc l u)→ᵇℂ,∃s:ℕ→ℕ,StrictMono s ∧
      TendstoUniformly (fun n (a:Icc l u)=>legAverage H ρ z r (φ (s n)) a) g atTop := by
  obtain ⟨C₀,C₁,hC₀,hC₁,hall⟩ := bump_average_L2_uniform_C1 hr hκ hs hb hρ hρsupp
  apply PinnedAverageCompactness.bounded_C1_subsequence
    (F:=fun n=>legAverage H ρ z r (φ n)) (C₀*R).toNNReal (C₁*R).toNNReal
  · intro n a ha
    exact (hall (φ n) (hφ n) a (hlu ha)).1
  · intro n a ha
    apply ENNReal.le_toNNReal_of_coe_le _ (ENNReal.mul_ne_top hC₀ hR)
    exact (hall (φ n) (hφ n) a (hlu ha)).2.1.trans (mul_le_mul_right (hbound n) C₀)
  · intro n a ha
    apply ENNReal.le_toNNReal_of_coe_le _ (ENNReal.mul_ne_top hC₁ hR)
    exact (hall (φ n) (hφ n) a (hlu ha)).2.2.trans (mul_le_mul_right (hbound n) C₁)

end
end Resonance.PinnedChartAverage
