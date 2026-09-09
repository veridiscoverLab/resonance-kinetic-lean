import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! A filter form of Scheffe's argument.  No moving majorant is assumed:
the minimum with the fixed limiting row is dominated by that row. -/
open MeasureTheory Filter Set
open scoped Topology
namespace Resonance.ScheffeRows
noncomputable section

theorem norm_sub_eq_add_sub_min (a b : ℝ) : ‖a-b‖ = a+b-2*min a b := by
  rw [Real.norm_eq_abs]
  rcases le_total a b with h | h
  · rw [min_eq_left h, abs_of_nonpos (sub_nonpos.mpr h)]
    ring
  · rw [min_eq_right h, abs_of_nonneg (sub_nonneg.mpr h)]
    ring

theorem integral_norm_sub_eq {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {f g : Ω → ℝ} (hf : Integrable f μ) (hg : Integrable g μ) :
    (∫ p, ‖f p-g p‖ ∂μ) =
      (∫ p, f p ∂μ)+(∫ p, g p ∂μ)-2*(∫ p, min (f p) (g p) ∂μ) := by
  simp_rw [norm_sub_eq_add_sub_min]
  have ha : Integrable (fun p => f p+g p) μ := hf.add hg
  have hb : Integrable (fun p => 2*min (f p) (g p)) μ := (hf.inf hg).const_mul 2
  rw [integral_sub ha hb, integral_add hf hg,
    integral_const_mul]

theorem tendsto_integral_norm_sub {Ω A : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {l : Filter A} [l.IsCountablyGenerated]
    (f : A → Ω → ℝ) (g : Ω → ℝ)
    (hf : ∀ a, Integrable (f a) μ) (hg : Integrable g μ)
    (hfn : ∀ a, 0 ≤ᵐ[μ] f a) (hgn : 0 ≤ᵐ[μ] g)
    (hpoint : ∀ᵐ p ∂μ, Tendsto (fun a => f a p) l (𝓝 (g p)))
    (hmass : Tendsto (fun a => ∫ p, f a p ∂μ) l (𝓝 (∫ p, g p ∂μ))) :
    Tendsto (fun a => ∫ p, ‖f a p-g p‖ ∂μ) l (𝓝 0) := by
  have hmin : Tendsto (fun a => ∫ p, min (f a p) (g p) ∂μ) l (𝓝 (∫ p, g p ∂μ)) := by
    have ht := tendsto_integral_filter_of_dominated_convergence
      (μ := μ) (l := l) (F := fun a p => min (f a p) (g p)) (f := g) g
    apply ht
    · exact Eventually.of_forall (fun a => (hf a |>.inf hg).aestronglyMeasurable)
    · apply Eventually.of_forall
      intro a
      filter_upwards [hfn a,hgn] with p hp hgp
      rw [Real.norm_eq_abs, abs_of_nonneg (le_min hp hgp)]
      exact min_le_right _ _
    · exact hg
    · filter_upwards [hpoint] with p hp
      simpa only [min_self] using hp.min (tendsto_const_nhds (x := g p))
  have ht := (hmass.add (tendsto_const_nhds (x := ∫ p, g p ∂μ))).sub
    ((tendsto_const_nhds (x := (2:ℝ))).mul hmin)
  simp only [show (∫ p, g p ∂μ)+(∫ p, g p ∂μ)-2*(∫ p, g p ∂μ)=0 by ring] at ht
  simpa only [integral_norm_sub_eq (hf _) hg] using ht

end
end Resonance.ScheffeRows
