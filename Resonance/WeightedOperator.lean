import Resonance.LpOperators
import Resonance.PhysicalCollisionForm
import Resonance.WeightedPhysicalForm

/-! The actual RJ-weighted complete form as a bounded nonnegative self-adjoint
operator on physical sharp-cube Lebesgue L². The weight and every comparison
are derived from the original positive RJ parameter domain. -/
open MeasureTheory
open scoped ENNReal

namespace Resonance.WeightedOperator
noncomputable section
open ResonantMeasure PhysicalMarginal PhysicalCollisionForm WeightedPhysicalForm

abbrev W (R : ℝ) (θ : Thermodynamics.Parameter) :=
  Lp ℝ 2 (WeightedJointMeasure.jointMeasure R θ)

def dominationConstant {R : ℝ} {θ : Thermodynamics.Parameter}
    (hθ : θ ∈ Thermodynamics.positiveDomain R) : ℝ≥0∞ :=
  (weighted_joint_domination hθ).choose

theorem dominationConstant_finite {R : ℝ} {θ : Thermodynamics.Parameter}
    (hθ : θ ∈ Thermodynamics.positiveDomain R) : dominationConstant hθ < ∞ :=
  (weighted_joint_domination hθ).choose_spec.1

theorem dominationConstant_dominates {R : ℝ} {θ : Thermodynamics.Parameter}
    (hθ : θ ∈ Thermodynamics.positiveDomain R) :
    WeightedJointMeasure.jointMeasure R θ ≤ dominationConstant hθ • pairingMeasure R :=
  (weighted_joint_domination hθ).choose_spec.2

def divide (R : ℝ) (θ : Thermodynamics.Parameter) : H R →L[ℝ] H R :=
  LpOperators.multiplyCLM (reciprocalProfile_memLp_top R θ)

theorem divide_ae (R : ℝ) (θ : Thermodynamics.Parameter) (f : H R) :
    divide R θ f =ᵐ[physicalMeasure R] (fun k => f k / WeightedJointMeasure.profile θ k) := by
  have h := LpOperators.multiply_ae (reciprocalProfile_memLp_top R θ) f
  simpa only [reciprocalProfile_eq_inv, div_eq_mul_inv] using h

def weightedChange {R : ℝ} {θ : Thermodynamics.Parameter}
    (hθ : θ ∈ Thermodynamics.positiveDomain R) : J R →L[ℝ] W R θ :=
  LpOperators.changeCLM (dominationConstant_finite hθ).ne (dominationConstant_dominates hθ)

def difference {R : ℝ} (hR : 0 ≤ R) {θ : Thermodynamics.Parameter}
    (hθ : θ ∈ Thermodynamics.positiveDomain R) : H R →L[ℝ] W R θ :=
  (weightedChange hθ).comp ((fullDifference hR).comp (divide R θ))

theorem difference_ae {R : ℝ} (hR : 0 ≤ R) {θ : Thermodynamics.Parameter}
    (hθ : θ ∈ Thermodynamics.positiveDomain R) (f : H R) :
    difference hR hθ f =ᵐ[WeightedJointMeasure.jointMeasure R θ] weightedDifference θ f := by
  have he := LpOperators.changeMeasure_ae (dominationConstant_finite hθ).ne
    (dominationConstant_dominates hθ) (fullDifference hR (divide R θ f))
  have hd := (WeightedJointMeasure.joint_absolutelyContinuous R θ).ae_eq
    (fullDifference_ae hR (divide R θ f))
  have hm (i : Fin 4) := (WeightedJointMeasure.joint_absolutelyContinuous R θ).ae_eq
    ((JointMultiplier.leg_quasiMeasurePreserving_cube R i).ae_eq (divide_ae R θ f))
  filter_upwards [he, hd, hm 0, hm 1, hm 2, hm 3] with k he hd h0 h1 h2 h3
  change LpOperators.changeMeasure (dominationConstant_finite hθ).ne
    (dominationConstant_dominates hθ) (fullDifference hR (divide R θ f)) k = _
  rw [he, hd]
  simp only [Function.comp_def] at h0 h1 h2 h3
  simp only [weightedDifference, completeDifference, h0, h1, h2, h3]

def operator {R : ℝ} (hR : 0 ≤ R) {θ : Thermodynamics.Parameter}
    (hθ : θ ∈ Thermodynamics.positiveDomain R) : H R →L[ℝ] H R :=
  (difference hR hθ).adjoint.comp (difference hR hθ)

theorem operator_pairing {R : ℝ} (hR : 0 ≤ R) {θ : Thermodynamics.Parameter}
    (hθ : θ ∈ Thermodynamics.positiveDomain R) (f g : H R) :
    inner ℝ f (operator hR hθ g) = inner ℝ (difference hR hθ f) (difference hR hθ g) :=
  ContinuousLinearMap.adjoint_inner_right (difference hR hθ) f (difference hR hθ g)

theorem operator_form {R : ℝ} (hR : 0 ≤ R) {θ : Thermodynamics.Parameter}
    (hθ : θ ∈ Thermodynamics.positiveDomain R) (f g : H R) :
    inner ℝ f (operator hR hθ g) = form R θ f g := by
  rw [operator_pairing, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [difference_ae hR hθ f, difference_ae hR hθ g] with k hf hg
  rw [hf, hg]
  change weightedDifference θ g k * weightedDifference θ f k = _
  ring

theorem operator_nonneg {R : ℝ} (hR : 0 ≤ R) {θ : Thermodynamics.Parameter}
    (hθ : θ ∈ Thermodynamics.positiveDomain R) (f : H R) :
    0 ≤ inner ℝ f (operator hR hθ f) := by
  rw [operator_form]
  exact form_nonneg R θ f

theorem operator_selfAdjoint {R : ℝ} (hR : 0 ≤ R) {θ : Thermodynamics.Parameter}
    (hθ : θ ∈ Thermodynamics.positiveDomain R) : IsSelfAdjoint (operator hR hθ) := by
  apply ContinuousLinearMap.isSelfAdjoint_iff'.mpr
  simp [operator, ContinuousLinearMap.adjoint_comp]

theorem operator_kernel {R : ℝ} (hR : 0 ≤ R) {θ : Thermodynamics.Parameter}
    (hθ : θ ∈ Thermodynamics.positiveDomain R) :
    (operator hR hθ).ker = (difference hR hθ).ker :=
  ContinuousLinearMap.ker_adjoint_comp_self (difference hR hθ)

theorem operator_eq_zero_iff {R : ℝ} (hR : 0 ≤ R) {θ : Thermodynamics.Parameter}
    (hθ : θ ∈ Thermodynamics.positiveDomain R) (f : H R) :
    operator hR hθ f = 0 ↔ ∀ᵐ k ∂pairingMeasure R,
      f (k 0) / WeightedJointMeasure.profile θ (k 0) +
      f (k 1) / WeightedJointMeasure.profile θ (k 1) =
      f (k 2) / WeightedJointMeasure.profile θ (k 2) +
      f (k 3) / WeightedJointMeasure.profile θ (k 3) := by
  have hk : operator hR hθ f = 0 ↔ difference hR hθ f = 0 := by
    change f ∈ (operator hR hθ).ker ↔ f ∈ (difference hR hθ).ker
    rw [operator_kernel]
  have hnorm : inner ℝ f (operator hR hθ f) = 0 ↔ difference hR hθ f = 0 := by
    rw [operator_pairing, real_inner_self_eq_norm_sq, sq_eq_zero_iff, norm_eq_zero]
  rw [hk, ← hnorm, operator_form]
  exact form_eq_zero_iff hR hθ (Lp.memLp f)

theorem maximal_physical_form_domain {R : ℝ} (hR : 0 ≤ R) {θ : Thermodynamics.Parameter}
    (hθ : θ ∈ Thermodynamics.positiveDomain R) :
    {f : H R | MemLp (weightedDifference θ f) 2 (WeightedJointMeasure.jointMeasure R θ)} = Set.univ := by
  ext f
  simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]
  exact weightedDifference_memLp hR hθ (Lp.memLp f)

end
end Resonance.WeightedOperator
