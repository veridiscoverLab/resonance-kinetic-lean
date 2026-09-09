import Resonance.ReferenceFrequencySpace

/-! Actual two-way measure transport between the fixed reference
frequency space and the original RJ marginal. -/
open MeasureTheory
open scoped ENNReal
namespace Resonance.ReferenceMarginalTransport
noncomputable section
open ResonantMeasure WeightedJointMeasure Thermodynamics FrequencyWeightedForm
open ReferenceFrequencySpace JointWeightComparison LpOperators

def toMarginalFactor (R M : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (M^4)*inverseLowerFactor R
def toReferenceFactor (R m : ℝ) : ℝ≥0∞ :=
  upperFactor R*(ENNReal.ofReal (m^4))⁻¹

theorem toMarginalFactor_finite (R M : ℝ) : toMarginalFactor R M≠∞ :=
  ENNReal.mul_ne_top ENNReal.ofReal_ne_top (inverseLowerFactor_finite R)
theorem toReferenceFactor_finite (R : ℝ) {m : ℝ} (hm : 0 < m) :
    toReferenceFactor R m≠∞ :=
  ENNReal.mul_ne_top (upperFactor_finite R)
    (ENNReal.inv_ne_top.mpr (ENNReal.ofReal_pos.mpr (pow_pos hm 4)).ne')

theorem actual_le_reference {R M : ℝ} (hR : 0≤R) {θ : Parameter}
    (hθ : θ∈positiveDomain R) (hb : ∀k∈cube R,profile θ k≤M) :
    marginal R θ≤toMarginalFactor R M • referenceMeasure R := by
  have hj : jointMeasure R θ≤ENNReal.ofReal (M^4) • jointMeasure R unitParameter := by
    rw [unit_joint]
    exact joint_weight_le hθ hb
  apply (marginal_of_joint_comparison hj).trans
  change ENNReal.ofReal (M^4) • marginal R unitParameter≤
    (ENNReal.ofReal (M^4)*inverseLowerFactor R) • referenceMeasure R
  rw [←smul_smul]
  intro s
  exact mul_le_mul' le_rfl (unit_le_reference hR s)

theorem reference_le_actual {R m : ℝ} (hR : 0≤R) (hm : 0 < m) {θ : Parameter}
    (hb : ∀k∈cube R,m≤profile θ k) :
    referenceMeasure R≤toReferenceFactor R m • marginal R θ := by
  have hj : jointMeasure R unitParameter≤(ENNReal.ofReal (m^4))⁻¹ • jointMeasure R θ := by
    rw [unit_joint]
    exact joint_weight_reverse hm hb
  apply (reference_le_unit hR).trans
  change upperFactor R • marginal R unitParameter≤
    (upperFactor R*(ENNReal.ofReal (m^4))⁻¹) • marginal R θ
  rw [←smul_smul]
  intro s
  exact mul_le_mul' le_rfl (marginal_of_joint_comparison hj s)

theorem actual_domination {R : ℝ} (hR : 0≤R) {θ : Parameter}
    (hθ : θ∈positiveDomain R) :
    ∃C : ℝ≥0∞,C≠∞ ∧ marginal R θ≤C • referenceMeasure R := by
  obtain ⟨M,_hM,hb⟩ := profile_bounded hθ
  exact ⟨toMarginalFactor R M,toMarginalFactor_finite R M,
    actual_le_reference hR hθ (fun k hk=>(le_abs_self _).trans (hb k hk))⟩

theorem reference_domination {R : ℝ} (hR : 0≤R) {θ : Parameter}
    (hθ : θ∈positiveDomain R) :
    ∃C : ℝ≥0∞,C≠∞ ∧ referenceMeasure R≤C • marginal R θ := by
  obtain ⟨m,hm,hb⟩ := FrequencyWeightedKernel.profile_uniform_lower hR hθ
  exact ⟨toReferenceFactor R m,toReferenceFactor_finite R hm,reference_le_actual hR hm hb⟩

def toMarginal {R : ℝ} (hR : 0≤R) {θ : Parameter} (hθ : θ∈positiveDomain R) :
    Space R→L[ℝ]H R θ :=
  changeCLM (Classical.choose_spec (actual_domination hR hθ)).1
    (Classical.choose_spec (actual_domination hR hθ)).2

def toReference {R : ℝ} (hR : 0≤R) {θ : Parameter} (hθ : θ∈positiveDomain R) :
    H R θ→L[ℝ]Space R :=
  changeCLM (Classical.choose_spec (reference_domination hR hθ)).1
    (Classical.choose_spec (reference_domination hR hθ)).2

theorem toMarginal_ae {R : ℝ} (hR : 0≤R) {θ : Parameter} (hθ : θ∈positiveDomain R)
    (f : Space R) : toMarginal hR hθ f=ᵐ[marginal R θ] f :=
  changeMeasure_ae (Classical.choose_spec (actual_domination hR hθ)).1
    (Classical.choose_spec (actual_domination hR hθ)).2 f

theorem toReference_ae {R : ℝ} (hR : 0≤R) {θ : Parameter} (hθ : θ∈positiveDomain R)
    (f : H R θ) : toReference hR hθ f=ᵐ[referenceMeasure R] f :=
  changeMeasure_ae (Classical.choose_spec (reference_domination hR hθ)).1
    (Classical.choose_spec (reference_domination hR hθ)).2 f

theorem toReference_toMarginal {R : ℝ} (hR : 0≤R) {θ : Parameter}
    (hθ : θ∈positiveDomain R) (f : Space R) :
    toReference hR hθ (toMarginal hR hθ f)=f :=
  FullDifferenceTransport.changeMeasure_inverse
    (Classical.choose_spec (reference_domination hR hθ)).1
    (Classical.choose_spec (actual_domination hR hθ)).1
    (Classical.choose_spec (reference_domination hR hθ)).2
    (Classical.choose_spec (actual_domination hR hθ)).2 f

theorem toMarginal_toReference {R : ℝ} (hR : 0≤R) {θ : Parameter}
    (hθ : θ∈positiveDomain R) (f : H R θ) :
    toMarginal hR hθ (toReference hR hθ f)=f :=
  FullDifferenceTransport.changeMeasure_inverse
    (Classical.choose_spec (actual_domination hR hθ)).1
    (Classical.choose_spec (reference_domination hR hθ)).1
    (Classical.choose_spec (actual_domination hR hθ)).2
    (Classical.choose_spec (reference_domination hR hθ)).2 f

end
end Resonance.ReferenceMarginalTransport
