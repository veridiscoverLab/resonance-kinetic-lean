import Resonance.FullDifferenceTransport
import Resonance.GramGapTransport

/-! Uniform coercivity on every compact positive RJ parameter family,
through the same physical full-quartet measure and actual marginals. -/
open MeasureTheory Set
open scoped ENNReal
namespace Resonance.UniformWeightedCoercivity
noncomputable section
open ResonantMeasure WeightedJointMeasure Thermodynamics FrequencyWeightedForm LpOperators
open JointWeightComparison FullDifferenceTransport ActualWeightedCoercivity

theorem profile_bounded_uniform_coercivity {R m M : ℝ} (hR : 0<R) (hm : 0 < m) :
    ∃δ : ℝ,0<δ ∧ ∀θ∈positiveDomain R,
      (∀k∈cube R,m≤profile θ k ∧ profile θ k≤M) → ∀f : H R θ,
      δ*‖f-(fullDifference R θ).ker.starProjection f‖^2≤‖fullDifference R θ f‖^2 := by
  let C : ℝ≥0∞ := ENNReal.ofReal (M^4)
  let D : ℝ≥0∞ := (ENNReal.ofReal (m^4))⁻¹
  have hC : C≠∞ := ENNReal.ofReal_ne_top
  have hD : D≠∞ := by
    apply ENNReal.inv_ne_top.mpr
    exact (ENNReal.ofReal_pos.mpr (pow_pos hm 4)).ne'
  let a := changeNorm C
  let b := changeNorm D
  have ha : 0≤a := ENNReal.toReal_nonneg
  have hb : 0≤b := ENNReal.toReal_nonneg
  obtain ⟨γ,hγ,hbase⟩ := CompactGramGap.orthogonal_norm_gap (fullDifference R unitParameter)
    (actual_gram_compact_perturbation hR (unitParameter_positive R))
  have hδ : 0<γ/(1+a*b) := div_pos hγ (by positivity)
  refine ⟨(γ/(1+a*b))^2,by positivity,?_⟩
  intro θ hθ hbound f
  have hCJ : jointMeasure R θ≤C • jointMeasure R unitParameter := by
    rw [unit_joint]
    exact joint_weight_le hθ (fun k hk=>(hbound k hk).2)
  have hDJ : jointMeasure R unitParameter≤D • jointMeasure R θ := by
    rw [unit_joint]
    exact joint_weight_reverse hm (fun k hk=>(hbound k hk).1)
  let E₀ : H R θ→L[ℝ]H R unitParameter := changeCLM hD (marginal_of_joint_comparison hDJ)
  let B₀ : H R unitParameter→L[ℝ]H R θ := changeCLM hC (marginal_of_joint_comparison hCJ)
  let F₀ : J R θ→L[ℝ]J R unitParameter := changeCLM hD hDJ
  have hnorm := GramGapTransport.transfer_norm_gap (fullDifference R θ)
    (fullDifference R unitParameter) E₀ B₀ F₀ ha hb hγ
    (changeMeasure_bound hC (marginal_of_joint_comparison hCJ))
    (changeMeasure_bound hD hDJ)
    (changeMeasure_inverse hC hD (marginal_of_joint_comparison hCJ)
      (marginal_of_joint_comparison hDJ))
    (actual_fullDifference_change hD hDJ)
    (fun v hv=>actual_kernel_change hC hCJ hv) hbase f
  simpa only [mul_pow] using pow_le_pow_left₀
    (mul_nonneg hδ.le (norm_nonneg _)) hnorm 2

theorem compact_parameter_coercivity {R : ℝ} (hR : 0<R) {K : Set Parameter}
    (hK : IsCompact K) (hpos : K⊆positiveDomain R) :
    ∃δ : ℝ,0<δ ∧ ∀θ∈K,∀f : H R θ,
      δ*‖f-(fullDifference R θ).ker.starProjection f‖^2≤
        ∫q,CollisionForm.rawDifference f q*CollisionForm.rawDifference f q∂jointMeasure R θ := by
  obtain ⟨m,M,hm,_hM,hbounds⟩ := compact_profile_bounds hR.le hK hpos
  obtain ⟨δ,hδ,hgap⟩ := profile_bounded_uniform_coercivity (M:=M) hR hm
  refine ⟨δ,hδ,?_⟩
  intro θ hθ f
  rw [←gram_integral,gram_pairing,real_inner_self_eq_norm_sq]
  exact hgap θ (hpos hθ) (hbounds θ hθ) f

end
end Resonance.UniformWeightedCoercivity
