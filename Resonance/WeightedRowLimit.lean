import Resonance.ScheffeRows

/-! Passage from unweighted L1 row continuity to a singular input
weight.  The uniform tail is an explicit input of this general lemma;
the sharp-cube application supplies it from the actual Newton estimate. -/
open MeasureTheory Set Filter Real
open scoped Topology
namespace Resonance.WeightedRowLimit
noncomputable section
set_option maxHeartbeats 600000

theorem weighted_difference_bound {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (w f g : Ω → ℝ) {B : ℝ} (hB : 0 ≤ B) {T : Set Ω} (hT : MeasurableSet T)
    (hw : ∀ p, 0 ≤ w p) (hf : ∀ p, 0 ≤ f p) (hg : ∀ p, 0 ≤ g p)
    (houtside : ∀ᵐ p ∂μ, p ∉ T → w p ≤ B)
    (hfi : Integrable f μ) (hgi : Integrable g μ)
    (hwfi : Integrable (fun p => w p*f p) μ) (hwgi : Integrable (fun p => w p*g p) μ) :
    (∫ p, ‖w p*f p-w p*g p‖ ∂μ) ≤
      B*(∫ p, ‖f p-g p‖ ∂μ) + (∫ p in T, w p*f p ∂μ) + (∫ p in T, w p*g p ∂μ) := by
  have hm : ∀ᵐ p ∂μ, ‖w p*f p-w p*g p‖ ≤ B*‖f p-g p‖+
      T.indicator (fun p => w p*f p) p+T.indicator (fun p => w p*g p) p := by
    filter_upwards [houtside] with p houtside
    by_cases hp : p ∈ T
    · rw [Set.indicator_of_mem hp,Set.indicator_of_mem hp]
      have hn := norm_sub_le (w p*f p) (w p*g p)
      rw [Real.norm_of_nonneg (mul_nonneg (hw p) (hf p)),
        Real.norm_of_nonneg (mul_nonneg (hw p) (hg p))] at hn
      linarith [mul_nonneg hB (norm_nonneg (f p-g p))]
    · rw [Set.indicator_of_notMem hp,Set.indicator_of_notMem hp,add_zero,add_zero,
        ← mul_sub, norm_mul,Real.norm_eq_abs,abs_of_nonneg (hw p)]
      exact mul_le_mul_of_nonneg_right (houtside hp) (norm_nonneg _)
  have hnorm : Integrable (fun p => ‖f p-g p‖) μ := (hfi.sub hgi).norm
  have hright : Integrable (fun p => B*‖f p-g p‖+
      T.indicator (fun p => w p*f p) p+T.indicator (fun p => w p*g p) p) μ :=
    ((hnorm.const_mul B).add (hwfi.indicator hT)).add (hwgi.indicator hT)
  have hh := integral_mono_ae ((hwfi.sub hwgi).norm) hright hm
  have hfirst : Integrable (fun p => B*‖f p-g p‖+T.indicator (fun p => w p*f p) p) μ :=
    (hnorm.const_mul B).add (hwfi.indicator hT)
  rw [integral_add hfirst (hwgi.indicator hT),
    integral_add (hnorm.const_mul B) (hwfi.indicator hT), integral_const_mul,
    integral_indicator hT,integral_indicator hT] at hh
  exact hh

theorem weighted_L1_tendsto {Ω A : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {l : Filter A} (s : Set A) (hs : ∀ᶠ a in l, a ∈ s)
    (w : Ω → ℝ) (f : A → Ω → ℝ) (g : Ω → ℝ)
    (hw : ∀ p, 0 ≤ w p) (hfn : ∀ a p, 0 ≤ f a p) (hgn : ∀ p, 0 ≤ g p)
    (hf : ∀ a, Integrable (f a) μ) (hg : Integrable g μ)
    (hwf : ∀ a, Integrable (fun p => w p*f a p) μ)
    (hwg : Integrable (fun p => w p*g p) μ)
    (hL1 : Tendsto (fun a => ∫ p, ‖f a p-g p‖ ∂μ) l (𝓝 0))
    (htail : ∀ ε : ℝ, 0 < ε → ∃ T : Set Ω, MeasurableSet T ∧ ∃ B : ℝ, 0 < B ∧
      (∀ᵐ p ∂μ, p ∉ T → w p ≤ B) ∧ (∀ a ∈ s, (∫ p in T, w p*f a p ∂μ) ≤ ε) ∧
      (∫ p in T, w p*g p ∂μ) ≤ ε) :
    Tendsto (fun a => ∫ p, ‖w p*f a p-w p*g p‖ ∂μ) l (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨T,hT,B,hB,houtside,hft,hgt⟩ := htail (ε/4) (by positivity)
  have he := (tendsto_order.mp hL1).2 (ε/(2*B)) (by positivity)
  filter_upwards [hs,he] with a ha he
  rw [Real.dist_eq,sub_zero,abs_of_nonneg (integral_nonneg (fun _ => norm_nonneg _))]
  have hb := weighted_difference_bound w (f a) g hB.le hT hw (hfn a) hgn houtside
    (hf a) hg (hwf a) hwg
  have ht := hft a ha
  have he' : B*(∫ p, ‖f a p-g p‖ ∂μ) < ε/2 := by
    have := (lt_div_iff₀ (show 0 < 2*B by positivity)).mp he
    nlinarith
  linarith

end
end Resonance.WeightedRowLimit
