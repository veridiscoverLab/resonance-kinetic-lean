import Resonance.UniformWeightedCoercivity

/-! The manuscript's fixed Hilbert space L2(D,nu_* dk), with its
literal reference frequency and its original zero-frequency corners. -/
open MeasureTheory Set
open scoped ENNReal
namespace Resonance.ReferenceFrequencySpace
noncomputable section
open ResonantMeasure WeightedJointMeasure CollisionFrequency FrequencyWeightedForm
open ActualPairNormalization JointWeightComparison

def referenceMeasure (R : ℝ) : Measure E :=
  (cubeVolume R).withDensity (fun k=>ENNReal.ofReal (referenceFrequency R k))

abbrev Space (R : ℝ) := Lp ℝ 2 (referenceMeasure R)

theorem unit_marginal_density {R : ℝ} (hR : 0≤R) :
    marginal R unitParameter=(cubeVolume R).withDensity
      (fun k=>ENNReal.ofReal (geometricFrequency R k)) := by
  rw [marginal_cube_density hR]
  congr 1
  funext k
  rw [marginalDensity,CollisionMarginalDensity.weighted_density_eq_frequency_global hR
    (unitParameter_positive R)]
  simp only [unit_profile,one_pow,one_mul,lossFrequency,unit_profile,inv_one,
    mul_one,geometricFrequency]

theorem reference_density_measurable (R : ℝ) :
    Measurable (fun k=>ENNReal.ofReal (referenceFrequency R k)) :=
  (CollisionMarginalDensity.lossFrequency_measurable R referenceProfile_continuous.measurable).ennreal_ofReal

theorem reference_support (R : ℝ) : ∀ᵐk∂referenceMeasure R,k∈cube R :=
  (withDensity_absolutelyContinuous _ _).ae_le (ae_restrict_mem (measurable_cube R))

theorem reference_volume_equivalent {R : ℝ} (hR : 0<R) :
    cubeVolume R≪referenceMeasure R ∧ referenceMeasure R≪cubeVolume R := by
  refine ⟨?_,withDensity_absolutelyContinuous _ _⟩
  apply withDensity_absolutelyContinuous' (reference_density_measurable R).aemeasurable
  filter_upwards [CornerInverseFrequency.referenceFrequency_positive_ae hR] with k hk
  exact (ENNReal.ofReal_pos.mpr hk).ne'

def upperFactor (R : ℝ) : ℝ≥0∞ := ENNReal.ofReal (1+9*R^2)
def inverseLowerFactor (R : ℝ) : ℝ≥0∞ := (ENNReal.ofReal (((1+9*R^2)⁻¹)^3))⁻¹

theorem geometric_density_measurable (R : ℝ) :
    Measurable (fun k=>ENNReal.ofReal (geometricFrequency R k)) := by
  have hm : Measurable (lossFrequency R (fun _ : E=>(1 : ℝ))) :=
    CollisionMarginalDensity.lossFrequency_measurable R measurable_const
  have he : lossFrequency R (fun _ : E=>(1 : ℝ))=geometricFrequency R := by
    funext k
    simp [lossFrequency,geometricFrequency]
  rw [he] at hm
  exact hm.ennreal_ofReal

theorem reference_le_unit {R : ℝ} (hR : 0≤R) :
    referenceMeasure R≤upperFactor R • marginal R unitParameter := by
  rw [unit_marginal_density hR,referenceMeasure,←withDensity_smul _ (geometric_density_measurable R)]
  apply withDensity_mono
  filter_upwards [ae_restrict_mem (measurable_cube R)] with k hk
  change ENNReal.ofReal (referenceFrequency R k)≤
    ENNReal.ofReal (1+9*R^2)*ENNReal.ofReal (geometricFrequency R k)
  rw [←ENNReal.ofReal_mul (by positivity : 0≤1+9*R^2)]
  exact ENNReal.ofReal_le_ofReal (referenceFrequency_geometric_bounds hR hk).2

theorem unit_le_reference {R : ℝ} (hR : 0≤R) :
    marginal R unitParameter ≤ inverseLowerFactor R • referenceMeasure R := by
  have hc : 0<((1+9*R^2)⁻¹)^3 := by positivity
  have hl : ENNReal.ofReal (((1+9*R^2)⁻¹)^3) • marginal R unitParameter≤referenceMeasure R := by
    rw [unit_marginal_density hR,referenceMeasure,←withDensity_smul _ (geometric_density_measurable R)]
    apply withDensity_mono
    filter_upwards [ae_restrict_mem (measurable_cube R)] with k hk
    rw [Pi.smul_apply,smul_eq_mul,←ENNReal.ofReal_mul hc.le]
    exact ENNReal.ofReal_le_ofReal (referenceFrequency_geometric_bounds hR hk).1
  have hh : inverseLowerFactor R •
      (ENNReal.ofReal (((1+9*R^2)⁻¹)^3) • marginal R unitParameter)≤
      inverseLowerFactor R • referenceMeasure R := by
    intro s
    exact mul_le_mul' le_rfl (hl s)
  simpa only [smul_smul,inverseLowerFactor,ENNReal.inv_mul_cancel
    (ENNReal.ofReal_pos.mpr hc).ne' ENNReal.ofReal_ne_top,one_smul] using hh

theorem upperFactor_finite (R : ℝ) : upperFactor R≠∞ := ENNReal.ofReal_ne_top
theorem inverseLowerFactor_finite (R : ℝ) : inverseLowerFactor R≠∞ := by
  unfold inverseLowerFactor
  exact ENNReal.inv_ne_top.mpr ((ENNReal.ofReal_pos.mpr (by positivity)).ne')

end
end Resonance.ReferenceFrequencySpace
