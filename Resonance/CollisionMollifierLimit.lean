import Resonance.CollisionConvolution
import Resonance.QuadraticPointwiseClosure
import Mathlib.Analysis.Calculus.BumpFunction.Convolution

/-! Actual normalized mollifiers recover a merely integrable invariant.
Lebesgue differentiation and closedness of the same five-dimensional family
are applied on one common full-measure set. -/
open Set MeasureTheory Filter Metric
open scoped Topology ContDiff Convolution

namespace Resonance.CollisionMollifierLimit
noncomputable section
open ResonantMeasure ContinuousCollisionInvariants CollisionConvolution QuadraticPointwiseClosure

def bump (δ : ℝ) (hδ : 0 < δ) (n : ℕ) : ContDiffBump (0 : E) where
  rIn := (δ/((n:ℝ)+1))/2
  rOut := δ/((n:ℝ)+1)
  rIn_pos := by positivity
  rIn_lt_rOut := by
    have : 0 < δ/((n:ℝ)+1) := by positivity
    linarith

theorem bump_radius_tendsto (δ : ℝ) (hδ : 0 < δ) :
    Tendsto (fun n => (bump δ hδ n).rOut) atTop (𝓝 0) := by
  have h := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul δ
  simpa only [bump, mul_one_div, mul_zero] using h

theorem bump_support_cube (δ : ℝ) (hδ : 0 < δ) (n : ℕ) :
    Function.support ((bump δ hδ n).normed (volume : Measure E)) ⊆ cube δ := by
  rw [ContDiffBump.support_normed_eq]
  intro x hx j
  have hn : δ/((n:ℝ)+1) ≤ δ := by
    apply (div_le_iff₀ (by positivity : 0 < (n:ℝ)+1)).mpr
    nlinarith [Nat.cast_nonneg (α := ℝ) n]
  have hx' : ‖x‖ < δ/((n:ℝ)+1) := by simpa only [mem_ball, dist_zero_right, bump] using hx
  exact (PiLp.norm_apply_le x j).trans (hx'.le.trans hn)

theorem actual_mollifier_ae_limit {f : E → ℝ} (hfi : Integrable f)
    (δ : ℝ) (hδ : 0 < δ) : ∀ᵐ x ∂(volume : Measure E),
      Tendsto (fun n => smooth ((bump δ hδ n).normed volume) f x) atTop (𝓝 (f x)) := by
  have hr : ∀ᶠ n in atTop, (bump δ hδ n).rOut ≤ 2*(bump δ hδ n).rIn := by
    exact Eventually.of_forall (fun n => by dsimp [bump]; linarith)
  exact ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable
    (bump_radius_tendsto δ hδ) hr hfi.locallyIntegrable

theorem integrable_invariant_inner_cube {r R : ℝ} (hr : 0 < r) (hrR : r < R)
    {f : E → ℝ} (hfm : Measurable f) (hfi : Integrable f) (hf : invariant R f) :
    ∃ b : Coefficients, ∀ᵐ x ∂(volume : Measure E).restrict (openCube r), f x = evaluate b x := by
  let δ := R-r
  have hδ : 0 < δ := sub_pos.mpr hrR
  let κ (n : ℕ) := (bump δ hδ n).normed (volume : Measure E)
  have hpoly (n : ℕ) := smooth_invariant_quadratic hr (by dsimp [δ]; linarith : r+δ ≤ R)
    (ContDiffBump.hasCompactSupport_normed (bump δ hδ n))
    (ContDiffBump.contDiff_normed (bump δ hδ n)) (bump_support_cube δ hδ n) hfm hfi hf
  choose c hc using hpoly
  let b (n : ℕ) : Coefficients := ⟨smooth (κ n) f 0, fderiv ℝ (smooth (κ n) f) 0, c n/2⟩
  have hb (n : ℕ) (x : E) (hx : x∈openCube r) : smooth (κ n) f x = evaluate (b n) x := hc n x hx
  let S : Set E := {x | x∈openCube r ∧ Tendsto (fun n => smooth (κ n) f x) atTop (𝓝 (f x))}
  obtain ⟨a,ha⟩ := pointwise_limit_polynomial S b f (fun x hx => by
    simpa only [← hb _ x hx.1] using hx.2)
  refine ⟨a,?_⟩
  rw [ae_restrict_iff' (openCube_isOpen r).measurableSet]
  filter_upwards [actual_mollifier_ae_limit hfi δ hδ] with x hx hxr
  exact ha x ⟨hxr,hx⟩

end
end Resonance.CollisionMollifierLimit
