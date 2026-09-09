import Resonance.PhysicalMarginal
import Resonance.WeightedJointMeasure

/-! The actual static Rayleigh--Jeans four-leg form on sharp-cube physical L².
All weights are evaluated on one common quartet. Integrability and the exact
zero-form relation are proved from the original positive parameter domain. -/
open MeasureTheory Set
open scoped ENNReal NNReal

namespace Resonance.WeightedPhysicalForm
noncomputable section
open ResonantMeasure PhysicalMarginal Thermodynamics

def reciprocalProfile (θ : Parameter) (k : E) : ℝ :=
  Entropy.denominator Entropy.fiveInvariants θ (WeightedJointMeasure.coordinates k)

theorem reciprocalProfile_continuous (θ : Parameter) : Continuous (reciprocalProfile θ) :=
  (Entropy.cube_denominator_continuous θ).comp WeightedJointMeasure.coordinates_continuous

theorem reciprocalProfile_eq_inv (θ : Parameter) (k : E) :
    reciprocalProfile θ k = (WeightedJointMeasure.profile θ k)⁻¹ := by
  simp [reciprocalProfile, WeightedJointMeasure.profile, Entropy.rj]

theorem reciprocalProfile_memLp_top (R : ℝ) (θ : Parameter) :
    MemLp (reciprocalProfile θ) ∞ (physicalMeasure R) := by
  obtain ⟨C, hC⟩ := (isCompact_Icc : IsCompact (Entropy.sharpCube R)).exists_bound_of_continuousOn
    (Entropy.cube_denominator_continuous θ).continuousOn
  apply memLp_top_of_bound (reciprocalProfile_continuous θ).measurable.aestronglyMeasurable C
  filter_upwards [ae_restrict_mem (measurable_cube R)] with k hk
  exact hC (WeightedJointMeasure.coordinates k) ((WeightedJointMeasure.coordinates_cube R k).mp hk)

theorem divide_profile_memLp (R : ℝ) (θ : Parameter) {f : E → ℝ}
    (hf : MemLp f 2 (physicalMeasure R)) :
    MemLp (fun k => f k / WeightedJointMeasure.profile θ k) 2 (physicalMeasure R) := by
  have h : MemLp (fun k => f k * reciprocalProfile θ k) 2 (physicalMeasure R) :=
    (reciprocalProfile_memLp_top R θ).mul' hf
  simpa only [div_eq_mul_inv, reciprocalProfile_eq_inv] using h

theorem weighted_joint_domination {R : ℝ} {θ : Parameter} (hθ : θ ∈ positiveDomain R) :
    ∃ C : ℝ≥0∞, C < ∞ ∧ WeightedJointMeasure.jointMeasure R θ ≤ C • pairingMeasure R := by
  obtain ⟨B, hB, hbound⟩ := WeightedJointMeasure.profile_bounded hθ
  refine ⟨ENNReal.ofReal (B ^ 4), ENNReal.ofReal_lt_top, ?_⟩
  have hweight : WeightedJointMeasure.weight θ ≤ᵐ[pairingMeasure R]
      (fun _ => ENNReal.ofReal (B ^ 4)) := by
    filter_upwards [ae_iff.mpr (pairing_supported_on_fullResonance R)] with k hk
    apply ENNReal.ofReal_le_ofReal
    calc
      (∏ i : Fin 4, WeightedJointMeasure.profile θ (k i)) ≤ ∏ _i : Fin 4, B := by
        apply Finset.prod_le_prod
        · intro i _
          exact (WeightedJointMeasure.profile_pos hθ (hk.1 i)).le
        · intro i _
          exact (le_abs_self _).trans (hbound _ (hk.1 i))
      _ = B ^ 4 := by simp
  simpa only [WeightedJointMeasure.jointMeasure, withDensity_const] using withDensity_mono hweight

theorem weighted_marginal_domination {R : ℝ} (hR : 0 ≤ R) {θ : Parameter}
    (hθ : θ ∈ positiveDomain R) :
    ∃ C : ℝ≥0∞, C < ∞ ∧ ∀ i : Fin 4,
      Measure.map (fun k : FourMomenta => k i) (WeightedJointMeasure.jointMeasure R θ) ≤
        C • physicalMeasure R := by
  obtain ⟨B, hB, hb⟩ := weighted_joint_domination hθ
  refine ⟨B * marginalConstant R, ENNReal.mul_lt_top hB (marginalConstant_finite R), ?_⟩
  intro i
  have hmap := Measure.map_mono hb (measurable_pi_apply i)
  rw [Measure.map_smul] at hmap
  apply hmap.trans
  rw [← smul_smul]
  intro s
  simp only [Measure.smul_apply, smul_eq_mul]
  exact mul_le_mul_of_nonneg_left (cube_marginal_domination hR i s) (zero_le B)

def weightedDifference (θ : Parameter) (f : E → ℝ) : FourMomenta → ℝ :=
  completeDifference (fun k => f k / WeightedJointMeasure.profile θ k)

theorem weightedDifference_memLp {R : ℝ} (hR : 0 ≤ R) {θ : Parameter}
    (hθ : θ ∈ positiveDomain R) {f : E → ℝ} (hf : MemLp f 2 (physicalMeasure R)) :
    MemLp (weightedDifference θ f) 2 (WeightedJointMeasure.jointMeasure R θ) := by
  obtain ⟨B, hB, hb⟩ := weighted_joint_domination hθ
  exact (cube_difference_memLp hR (divide_profile_memLp R θ hf)).of_measure_le_smul hB.ne hb

def form (R : ℝ) (θ : Parameter) (f g : E → ℝ) : ℝ :=
  ∫ k, weightedDifference θ f k * weightedDifference θ g k
    ∂WeightedJointMeasure.jointMeasure R θ

theorem form_integrable {R : ℝ} (hR : 0 ≤ R) {θ : Parameter}
    (hθ : θ ∈ positiveDomain R) {f g : E → ℝ}
    (hf : MemLp f 2 (physicalMeasure R)) (hg : MemLp g 2 (physicalMeasure R)) :
    Integrable (fun k => weightedDifference θ f k * weightedDifference θ g k)
      (WeightedJointMeasure.jointMeasure R θ) :=
  (weightedDifference_memLp hR hθ hf).integrable_mul (weightedDifference_memLp hR hθ hg)

theorem form_symmetric (R : ℝ) (θ : Parameter) (f g : E → ℝ) :
    form R θ f g = form R θ g f := by
  unfold form
  simp_rw [mul_comm]

theorem form_nonneg (R : ℝ) (θ : Parameter) (f : E → ℝ) : 0 ≤ form R θ f f :=
  integral_nonneg (fun _ => mul_self_nonneg _)

theorem form_eq_zero_iff {R : ℝ} (hR : 0 ≤ R) {θ : Parameter}
    (hθ : θ ∈ positiveDomain R) {f : E → ℝ} (hf : MemLp f 2 (physicalMeasure R)) :
    form R θ f f = 0 ↔ ∀ᵐ k ∂pairingMeasure R,
      f (k 0) / WeightedJointMeasure.profile θ (k 0) +
      f (k 1) / WeightedJointMeasure.profile θ (k 1) =
      f (k 2) / WeightedJointMeasure.profile θ (k 2) +
      f (k 3) / WeightedJointMeasure.profile θ (k 3) := by
  have hi := form_integrable hR hθ hf hf
  have he := integral_eq_zero_iff_of_nonneg_ae
    (Filter.Eventually.of_forall (fun k => mul_self_nonneg (weightedDifference θ f k))) hi
  change (∫ k, weightedDifference θ f k * weightedDifference θ f k
    ∂WeightedJointMeasure.jointMeasure R θ) = 0 ↔ _
  rw [he]
  constructor
  · intro hz
    have hz' := (WeightedJointMeasure.pairing_absolutelyContinuous hθ).ae_le hz
    filter_upwards [hz'] with k hk
    have hd : weightedDifference θ f k = 0 := mul_self_eq_zero.mp hk
    dsimp [weightedDifference, completeDifference] at hd
    linarith
  · intro hz
    have hz' := (WeightedJointMeasure.joint_absolutelyContinuous R θ).ae_le hz
    filter_upwards [hz'] with k hk
    have hd : weightedDifference θ f k = 0 := by
      dsimp [weightedDifference, completeDifference]
      linarith
    simp [hd]

end
end Resonance.WeightedPhysicalForm
