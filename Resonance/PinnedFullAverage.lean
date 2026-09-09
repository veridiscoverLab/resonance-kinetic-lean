import Resonance.PinnedChartAverage
import Resonance.PinnedAverageDefect

/-! The three source terms below belong to one resonance graph and one
circle function.  Their sum has the original signs; both compactness and
the defect estimate preserve this common input. -/
open Real MeasureTheory Set Filter
open scoped ENNReal NNReal Topology ContDiff BoundedContinuousFunction
namespace Resonance.PinnedFullAverage
noncomputable section
open Resonance.PinnedSmoothing Resonance.PinnedLocalSmooth
open Resonance.PinnedPeriodicity Resonance.PinnedClassificationFinal
open Resonance.PinnedChartAverage

def sourceChart (H : ℝ×ℝ→ℝ) (i : Fin 3) (p : ℝ×ℝ) : ℝ :=
  ![p.2,p.1+H p-p.2,H p] i

def fullAverage (H : ℝ×ℝ→ℝ) (ρ : ℝ→ℝ) (z r : ℝ)
    (φ : PinnedPeriodicity.Circle→ℂ) : ℝ→ℂ :=
  legAverage (sourceChart H 0) ρ z r φ +
    legAverage (sourceChart H 1) ρ z r φ - legAverage (sourceChart H 2) ρ z r φ

theorem source_charts_regular {H : ℝ×ℝ→ℝ} {x z r κ : ℝ}
    (_hκ : 0<κ)
    (hs : ContDiffOn ℝ ∞ H (Metric.ball x r ×ˢ Metric.ball z r))
    (hb : ∀p∈Metric.ball x r ×ˢ Metric.ball z r,
      κ≤|partialZ H p| ∧ κ≤|partialZ H p-1|) (i:Fin 3) :
    ContDiffOn ℝ ∞ (sourceChart H i) (Metric.ball x r ×ˢ Metric.ball z r) ∧
    ∀p∈Metric.ball x r ×ˢ Metric.ball z r,
      min κ 1≤|partialZ (sourceChart H i) p| := by
  have hsm (j:Fin 3) : ContDiffOn ℝ ∞ (sourceChart H j)
      (Metric.ball x r ×ˢ Metric.ball z r) := by
    fin_cases j
    · exact contDiffOn_snd
    · exact (contDiffOn_fst.add hs).sub contDiffOn_snd
    · exact hs
  refine ⟨hsm i,?_⟩
  intro p hp
  have hd := ((hs.differentiableOn (by simp)) p hp).differentiableAt
    ((Metric.isOpen_ball.prod Metric.isOpen_ball).mem_nhds hp)
  have hdi := (((hsm i).differentiableOn (by simp)) p hp).differentiableAt
    ((Metric.isOpen_ball.prod Metric.isOpen_ball).mem_nhds hp)
  have hslice := partialZ_hasDerivAt hdi
  fin_cases i
  · change min κ 1≤|partialZ (sourceChart H 0) p|
    have he : partialZ (sourceChart H 0) p=1 :=
      hslice.unique (hasDerivAt_id p.2)
    rw [he,abs_one]
    exact min_le_right _ _
  · change min κ 1≤|partialZ (sourceChart H 1) p|
    have he : partialZ (sourceChart H 1) p=partialZ H p-1 := by
      exact hslice.unique (by
        simpa only [zero_add] using
          ((hasDerivAt_const p.2 p.1).add (partialZ_hasDerivAt hd)).sub (hasDerivAt_id p.2))
    rw [he]
    exact (min_le_left κ 1).trans (hb p hp).2
  · exact (min_le_left κ 1).trans (hb p hp).1

theorem full_average_L2_uniform_C1 {H : ℝ×ℝ→ℝ} {x z r κ : ℝ}
    (hr : 0<r) (hκ : 0<κ)
    (hs : ContDiffOn ℝ ∞ H (Metric.ball x r ×ˢ Metric.ball z r))
    (hb : ∀p∈Metric.ball x r ×ˢ Metric.ball z r,
      κ≤|partialZ H p| ∧ κ≤|partialZ H p-1|)
    {ρ : ℝ→ℝ} (hρ : ContDiff ℝ ∞ ρ)
    (hρsupp : tsupport ρ ⊆ Metric.ball z (r/8)) :
    ∃ C₀ C₁ : ℝ≥0∞, C₀≠⊤ ∧ C₁≠⊤ ∧
      ∀ φ : PinnedPeriodicity.Circle→ℂ, MemLp φ 2 circleHaar →
      ∀ a∈Metric.ball x (r/4),
        DifferentiableAt ℝ (fullAverage H ρ z r φ) a ∧
        ‖fullAverage H ρ z r φ a‖ₑ ≤ C₀*eLpNorm φ 2 circleHaar ∧
        ‖deriv (fullAverage H ρ z r φ) a‖ₑ ≤ C₁*eLpNorm φ 2 circleHaar := by
  have hleg (i:Fin 3) := bump_average_L2_uniform_C1 hr (lt_min hκ zero_lt_one)
    (source_charts_regular hκ hs hb i).1 (source_charts_regular hκ hs hb i).2 hρ hρsupp
  choose C₀ C₁ hC₀ hC₁ hall using hleg
  refine ⟨C₀ 0+C₀ 1+C₀ 2,C₁ 0+C₁ 1+C₁ 2,
    ENNReal.add_ne_top.mpr ⟨ENNReal.add_ne_top.mpr ⟨hC₀ 0,hC₀ 1⟩,hC₀ 2⟩,
    ENNReal.add_ne_top.mpr ⟨ENNReal.add_ne_top.mpr ⟨hC₁ 0,hC₁ 1⟩,hC₁ 2⟩,?_⟩
  intro φ hφ a ha
  have hd (i:Fin 3) := (hall i φ hφ a ha).1
  have hsum (u v w:ℂ) : ‖u+v-w‖ₑ ≤ ‖u‖ₑ+‖v‖ₑ+‖w‖ₑ :=
    enorm_sub_le.trans (add_le_add (enorm_add_le u v) le_rfl)
  refine ⟨((hd 0).add (hd 1)).sub (hd 2),?_,?_⟩
  · apply (hsum _ _ _).trans
    simpa only [add_mul] using add_le_add
      (add_le_add (hall 0 φ hφ a ha).2.1 (hall 1 φ hφ a ha).2.1)
      (hall 2 φ hφ a ha).2.1
  · rw [fullAverage,deriv_sub ((hd 0).add (hd 1)) (hd 2),deriv_add (hd 0) (hd 1)]
    apply (hsum _ _ _).trans
    simpa only [add_mul] using add_le_add
      (add_le_add (hall 0 φ hφ a ha).2.2 (hall 1 φ hφ a ha).2.2)
      (hall 2 φ hφ a ha).2.2

theorem full_average_L2_subsequence {H : ℝ×ℝ→ℝ} {x z r κ l u : ℝ}
    (hr : 0<r) (hκ : 0<κ)
    (hs : ContDiffOn ℝ ∞ H (Metric.ball x r ×ˢ Metric.ball z r))
    (hb : ∀p∈Metric.ball x r ×ˢ Metric.ball z r,
      κ≤|partialZ H p| ∧ κ≤|partialZ H p-1|)
    {ρ : ℝ→ℝ} (hρ : ContDiff ℝ ∞ ρ)
    (hρsupp : tsupport ρ ⊆ Metric.ball z (r/8))
    (hlu : Icc l u ⊆ Metric.ball x (r/4))
    {φ : ℕ→PinnedPeriodicity.Circle→ℂ} (hφ : ∀n,MemLp (φ n) 2 circleHaar)
    {R : ℝ≥0∞} (hR : R≠⊤) (hbound : ∀n,eLpNorm (φ n) 2 circleHaar≤R) :
    ∃g:(Icc l u)→ᵇℂ,∃s:ℕ→ℕ,StrictMono s ∧
      TendstoUniformly (fun n (a:Icc l u)=>fullAverage H ρ z r (φ (s n)) a) g atTop := by
  obtain ⟨C₀,C₁,hC₀,hC₁,hall⟩ := full_average_L2_uniform_C1 hr hκ hs hb hρ hρsupp
  apply PinnedAverageCompactness.bounded_C1_subsequence
    (F:=fun n=>fullAverage H ρ z r (φ n)) (C₀*R).toNNReal (C₁*R).toNNReal
  · intro n a ha
    exact (hall (φ n) (hφ n) a (hlu ha)).1
  · intro n a ha
    apply ENNReal.le_toNNReal_of_coe_le _ (ENNReal.mul_ne_top hC₀ hR)
    exact (hall (φ n) (hφ n) a (hlu ha)).2.1.trans (mul_le_mul_right (hbound n) C₀)
  · intro n a ha
    apply ENNReal.le_toNNReal_of_coe_le _ (ENNReal.mul_ne_top hC₁ hR)
    exact (hall (φ n) (hφ n) a (hlu ha)).2.2.trans (mul_le_mul_right (hbound n) C₁)

end
end Resonance.PinnedFullAverage
