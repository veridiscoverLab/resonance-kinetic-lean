import Resonance.ReferenceMarginalTransport

/-! The literal physical change h=u/N, as inverse continuous linear
maps on the fixed reference-frequency space and the actual marginal. -/
open MeasureTheory
open scoped ENNReal
namespace Resonance.PhysicalFrequencyCoordinates
noncomputable section
open ResonantMeasure WeightedJointMeasure Thermodynamics FrequencyWeightedForm
open ReferenceFrequencySpace ReferenceMarginalTransport LpOperators

theorem multiply_cancel {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {w v : X→ℝ} (hw : MemLp w ∞ μ) (hv : MemLp v ∞ μ)
    (hprod : ∀ᵐx∂μ,w x*v x=1) (f : Lp ℝ 2 μ) :
    multiply hw (multiply hv f)=f := by
  apply Lp.ext
  filter_upwards [multiply_ae hw (multiply hv f),multiply_ae hv f,hprod] with x h1 h2 hp
  rw [h1,h2]
  calc
    (f x*v x)*w x=f x*(w x*v x) := by ring
    _ = f x := by rw [hp,mul_one]

theorem profile_memLp_reference {R : ℝ} {θ : Parameter} (hθ : θ∈positiveDomain R) :
    MemLp (profile θ) ∞ (referenceMeasure R) := by
  obtain ⟨M,_hM,hb⟩ := profile_bounded hθ
  apply memLp_top_of_bound (profile_measurable θ).aestronglyMeasurable M
  filter_upwards [reference_support R] with k hk
  simpa only [Real.norm_eq_abs] using hb k hk

theorem reciprocal_memLp_reference {R : ℝ} (hR : 0≤R) {θ : Parameter}
    (hθ : θ∈positiveDomain R) :
    MemLp (fun k=>(profile θ k)⁻¹) ∞ (referenceMeasure R) := by
  obtain ⟨m,hm,hb⟩ := FrequencyWeightedKernel.profile_uniform_lower hR hθ
  apply memLp_top_of_bound (profile_measurable θ).inv.aestronglyMeasurable (m⁻¹)
  filter_upwards [reference_support R] with k hk
  rw [Real.norm_eq_abs,abs_of_pos (inv_pos.mpr (profile_pos hθ hk))]
  exact inv_anti₀ hm (hb k hk)

theorem profile_inverse_product {R : ℝ} {θ : Parameter} (hθ : θ∈positiveDomain R) :
    ∀ᵐk∂referenceMeasure R,profile θ k*(profile θ k)⁻¹=1 := by
  filter_upwards [reference_support R] with k hk
  exact mul_inv_cancel₀ (profile_pos hθ hk).ne'

def forward {R : ℝ} (hR : 0≤R) {θ : Parameter} (hθ : θ∈positiveDomain R) :
    Space R→L[ℝ]H R θ :=
  (toMarginal hR hθ).comp (multiplyCLM (reciprocal_memLp_reference hR hθ))

def backward {R : ℝ} (hR : 0≤R) {θ : Parameter} (hθ : θ∈positiveDomain R) :
    H R θ→L[ℝ]Space R :=
  (multiplyCLM (profile_memLp_reference hθ)).comp (toReference hR hθ)

theorem forward_ae {R : ℝ} (hR : 0≤R) {θ : Parameter} (hθ : θ∈positiveDomain R)
    (u : Space R) : forward hR hθ u=ᵐ[marginal R θ] (fun k=>u k/profile θ k) := by
  have hac : marginal R θ≪referenceMeasure R :=
    Measure.absolutelyContinuous_of_le_smul (Classical.choose_spec (actual_domination hR hθ)).2
  filter_upwards [toMarginal_ae hR hθ (multiply (reciprocal_memLp_reference hR hθ) u),
    hac.ae_eq (multiply_ae (reciprocal_memLp_reference hR hθ) u)] with k h1 h2
  exact h1.trans (h2.trans (div_eq_mul_inv (u k) (profile θ k)).symm)

theorem backward_ae {R : ℝ} (hR : 0≤R) {θ : Parameter} (hθ : θ∈positiveDomain R)
    (f : H R θ) : backward hR hθ f=ᵐ[referenceMeasure R] (fun k=>f k*profile θ k) := by
  filter_upwards [multiply_ae (profile_memLp_reference hθ) (toReference hR hθ f),
    toReference_ae hR hθ f] with k h1 h2
  exact h1.trans (congrArg (fun a=>a*profile θ k) h2)

theorem backward_forward {R : ℝ} (hR : 0≤R) {θ : Parameter} (hθ : θ∈positiveDomain R)
    (u : Space R) : backward hR hθ (forward hR hθ u)=u := by
  change multiply (profile_memLp_reference hθ)
    (toReference hR hθ (toMarginal hR hθ (multiply (reciprocal_memLp_reference hR hθ) u)))=u
  rw [toReference_toMarginal]
  exact multiply_cancel _ _ (profile_inverse_product hθ) u

theorem forward_backward {R : ℝ} (hR : 0≤R) {θ : Parameter} (hθ : θ∈positiveDomain R)
    (f : H R θ) : forward hR hθ (backward hR hθ f)=f := by
  change toMarginal hR hθ (multiply (reciprocal_memLp_reference hR hθ)
    (multiply (profile_memLp_reference hθ) (toReference hR hθ f)))=f
  have hp : ∀ᵐk∂referenceMeasure R,(profile θ k)⁻¹*profile θ k=1 := by
    filter_upwards [profile_inverse_product hθ] with k hk
    rwa [mul_comm]
  rw [multiply_cancel _ _ hp,toMarginal_toReference]

def physicalDifference {R : ℝ} (hR : 0≤R) {θ : Parameter} (hθ : θ∈positiveDomain R) :
    Space R→L[ℝ]J R θ := (fullDifference R θ).comp (forward hR hθ)

theorem physicalDifference_ae {R : ℝ} (hR : 0≤R) {θ : Parameter}
    (hθ : θ∈positiveDomain R) (u : Space R) :
    physicalDifference hR hθ u=ᵐ[jointMeasure R θ]
      CollisionForm.rawDifference (fun k=>u k/profile θ k) := by
  have hh := forward_ae hR hθ u
  filter_upwards [fullDifference_ae R θ (forward hR hθ u),
    (all_legs_preserve R θ 0).quasiMeasurePreserving.ae_eq hh,
    (all_legs_preserve R θ 1).quasiMeasurePreserving.ae_eq hh,
    (all_legs_preserve R θ 2).quasiMeasurePreserving.ae_eq hh,
    (all_legs_preserve R θ 3).quasiMeasurePreserving.ae_eq hh] with q hq h0 h1 h2 h3
  change fullDifference R θ (forward hR hθ u) q=_
  rw [hq]
  simp only [Function.comp_def] at h0 h1 h2 h3
  simp only [CollisionForm.rawDifference,h0,h1,h2,h3]

end
end Resonance.PhysicalFrequencyCoordinates
