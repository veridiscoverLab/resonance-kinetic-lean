import Resonance.ActualPairKernels
import Resonance.CornerInverseFrequency

/-! The inverse of the actual RJ one-leg marginal is controlled by the
original reference collision frequency on the same physical cube. -/
open MeasureTheory Set
open scoped ENNReal
namespace Resonance.MarginalInverseBounds
noncomputable section
open ResonantMeasure WeightedJointMeasure ActualPairNormalization
open CollisionFrequency FrequencyWeightedKernel CornerInverseFrequency

theorem marginal_reference_lower {R : ℝ} (hR : 0<R) {θ : Thermodynamics.Parameter}
    (hθ : θ∈Thermodynamics.positiveDomain R) :
    ∃c : ℝ,0<c ∧ ∀k∈cube R,
      ENNReal.ofReal (c*referenceFrequency R k) ≤ marginalDensity R θ k := by
  obtain ⟨m,hm,hml⟩ := profile_uniform_lower hR.le hθ
  have hB : 0<1+9*R^2 := by positivity
  refine ⟨m^4/(1+9*R^2),by positivity,?_⟩
  intro k hk
  apply le_trans (ENNReal.ofReal_le_ofReal ?_)
    (density_geometric_lower hR.le hm hml k)
  calc
    m^4/(1+9*R^2)*referenceFrequency R k ≤
        m^4/(1+9*R^2)*((1+9*R^2)*geometricFrequency R k) :=
      mul_le_mul_of_nonneg_left (referenceFrequency_geometric_bounds hR.le hk).2
        (by positivity)
    _ = m^4*geometricFrequency R k := by field_simp

def referenceInverse (R : ℝ) (k : E) : ℝ≥0∞ :=
  ENNReal.ofReal ((referenceFrequency R k)⁻¹)

theorem referenceInverse_measurable (R : ℝ) : Measurable (referenceInverse R) :=
  (CollisionMarginalDensity.lossFrequency_measurable R
    referenceProfile_continuous.measurable).inv.ennreal_ofReal

theorem referenceInverse_integral_finite {R : ℝ} (hR : 0<R) :
    (∫⁻k,referenceInverse R k∂cubeVolume R)<∞ := by
  have hi := (reference_inverse_integrable hR).hasFiniteIntegral
  rw [hasFiniteIntegral_iff_ofReal] at hi
  · exact hi
  · filter_upwards [referenceFrequency_positive_ae hR] with k hk
    exact (inv_pos.mpr hk).le

theorem marginal_inverse_reference_bound {R : ℝ} (hR : 0<R)
    {θ : Thermodynamics.Parameter} (hθ : θ∈Thermodynamics.positiveDomain R) :
    ∃A : ℝ≥0∞,A≠∞ ∧ ∀ᵐk∂cubeVolume R,
      (marginalDensity R θ k)⁻¹≤A*referenceInverse R k := by
  obtain ⟨c,hc,hcl⟩ := marginal_reference_lower hR hθ
  refine ⟨ENNReal.ofReal c⁻¹,ENNReal.ofReal_ne_top,?_⟩
  filter_upwards [ae_restrict_mem (measurable_cube R),referenceFrequency_positive_ae hR]
    with k hk hp
  calc
    (marginalDensity R θ k)⁻¹ ≤ (ENNReal.ofReal (c*referenceFrequency R k))⁻¹ :=
      ENNReal.inv_le_inv' (hcl k hk)
    _ = ENNReal.ofReal c⁻¹*referenceInverse R k := by
      rw [←ENNReal.ofReal_inv_of_pos (mul_pos hc hp),mul_inv_rev,
        ENNReal.ofReal_mul (inv_pos.mpr hp).le]
      exact mul_comm _ _

theorem marginal_inverse_integral_finite {R : ℝ} (hR : 0<R)
    {θ : Thermodynamics.Parameter} (hθ : θ∈Thermodynamics.positiveDomain R) :
    (∫⁻k,(marginalDensity R θ k)⁻¹∂cubeVolume R)<∞ := by
  obtain ⟨A,hA,hb⟩ := marginal_inverse_reference_bound hR hθ
  apply lt_of_le_of_lt (lintegral_mono_ae hb)
  rw [lintegral_const_mul A (referenceInverse_measurable R)]
  exact ENNReal.mul_lt_top hA.lt_top (referenceInverse_integral_finite hR)

end
end Resonance.MarginalInverseBounds
