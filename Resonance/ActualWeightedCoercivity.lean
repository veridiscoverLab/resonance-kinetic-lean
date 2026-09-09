import Resonance.CrossPairCompact
import Resonance.CompactGramGap

/-! Coercivity of the same complete four-leg Gram form.  Both compact
cross terms are now proved from their original sharp-cube measures. -/
open MeasureTheory
namespace Resonance.ActualWeightedCoercivity
noncomputable section
open ResonantMeasure WeightedJointMeasure FrequencyWeightedForm FrequencyGramDecomposition

theorem actual_gram_compact_perturbation {R : ℝ} (hR : 0<R)
    {θ : Thermodynamics.Parameter} (hθ : θ∈Thermodynamics.positiveDomain R) :
    IsCompactOperator (gram R θ-1 : H R θ→L[ℝ]H R θ) := by
  have he : gram R θ-1=cross R θ 0 1-(2 : ℝ) • cross R θ 0 2 := by
    rw [gram_eq_identity_add_cross]
    abel
  rw [he]
  exact (IncomingPairCompact.actual_cross01_compact hR hθ).sub
    ((CrossPairCompact.actual_cross02_compact hR hθ).smul (2 : ℝ))

theorem actual_projected_coercivity {R : ℝ} (hR : 0<R)
    {θ : Thermodynamics.Parameter} (hθ : θ∈Thermodynamics.positiveDomain R) :
    ∃δ : ℝ,0<δ ∧ ∀f : H R θ,
      δ*‖f-(fullDifference R θ).ker.starProjection f‖^2≤
        ∫q,CollisionForm.rawDifference f q*CollisionForm.rawDifference f q∂jointMeasure R θ := by
  obtain ⟨δ,hδ,hgap⟩ := CompactGramGap.projected_square_gap (fullDifference R θ)
    (actual_gram_compact_perturbation hR hθ)
  refine ⟨δ,hδ,fun f=>?_⟩
  rw [←gram_integral,gram_pairing,real_inner_self_eq_norm_sq]
  exact hgap f

theorem actual_orthogonal_coercivity {R : ℝ} (hR : 0<R)
    {θ : Thermodynamics.Parameter} (hθ : θ∈Thermodynamics.positiveDomain R) :
    ∃δ : ℝ,0<δ ∧ ∀f : H R θ,f∈(fullDifference R θ).kerᗮ →
      δ*‖f‖^2≤∫q,CollisionForm.rawDifference f q*CollisionForm.rawDifference f q∂jointMeasure R θ := by
  obtain ⟨γ,hγ,hgap⟩ := CompactGramGap.orthogonal_norm_gap (fullDifference R θ)
    (actual_gram_compact_perturbation hR hθ)
  refine ⟨γ^2,by positivity,?_⟩
  intro f hf
  rw [←gram_integral,gram_pairing,real_inner_self_eq_norm_sq]
  simpa only [mul_pow] using pow_le_pow_left₀
    (mul_nonneg hγ.le (norm_nonneg f)) (hgap f hf) 2

theorem actual_kernel_classification {R : ℝ} (hR : 0<R)
    {θ : Thermodynamics.Parameter} (hθ : θ∈Thermodynamics.positiveDomain R)
    (f : H R θ) : f∈(fullDifference R θ).ker ↔
      ∃!b : QuadraticPointwiseClosure.Coefficients,
        (f : E→ℝ)=ᵐ[volume.restrict (cube R)] QuadraticPointwiseClosure.evaluate b := by
  rw [←gram_kernel]
  exact FrequencyWeightedKernel.actual_weighted_kernel_iff hR hθ f

end
end Resonance.ActualWeightedCoercivity
