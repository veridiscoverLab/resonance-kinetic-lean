import Resonance.NormalizedPairDensity
import Resonance.IncomingPairDensity

/-! The original marginal normalization on the physical closed cube.
Strict positivity is proved only almost everywhere, so the original
zero-frequency corners are retained throughout. -/
open MeasureTheory Set
open scoped ENNReal
namespace Resonance.ActualPairNormalization
noncomputable section
open ResonantMeasure WeightedJointMeasure CollisionMarginalDensity
open FrequencyWeightedForm FrequencyWeightedKernel

def cubeVolume (R : ℝ) : Measure E := volume.restrict (cube R)

theorem cubeVolume_finite (R : ℝ) : IsFiniteMeasure (cubeVolume R) :=
  ⟨by simpa only [cubeVolume,Measure.restrict_apply_univ] using
    (FiberContinuity.cube_isCompact R).measure_lt_top⟩

def marginalDensity (R : ℝ) (θ : Thermodynamics.Parameter) : E→ℝ≥0∞ :=
  fiberDensity R (weight θ)

theorem marginalDensity_measurable (R : ℝ) (θ : Thermodynamics.Parameter) :
    Measurable (marginalDensity R θ) := fiberDensity_measurable (weight_measurable θ)

theorem marginal_cube_density {R : ℝ} (hR : 0≤R) (θ : Thermodynamics.Parameter) :
    marginal R θ=(cubeVolume R).withDensity (marginalDensity R θ) := by
  have hs : ∀ᵐ k∂marginal R θ,k∈cube R :=
    (marginal_absolutelyContinuous_cube R θ 0).ae_le (ae_restrict_mem (measurable_cube R))
  calc
    _ = (marginal R θ).restrict (cube R) := (Measure.restrict_eq_self_of_ae_mem hs).symm
    _ = _ := by
      rw [marginal,weighted_all_marginals hR θ 0,restrict_withDensity (measurable_cube R)]
      rfl

theorem marginalDensity_finite {R : ℝ} (hR : 0≤R) {θ : Thermodynamics.Parameter}
    (hθ : θ∈Thermodynamics.positiveDomain R) (k : E) : marginalDensity R θ k≠∞ := by
  rw [marginalDensity,weighted_density_eq_frequency_global hR hθ]
  exact ENNReal.ofReal_ne_top

theorem marginalDensity_valid_ae {R : ℝ} (hR : 0<R) {θ : Thermodynamics.Parameter}
    (hθ : θ∈Thermodynamics.positiveDomain R) :
    ∀ᵐ k∂cubeVolume R,marginalDensity R θ k≠0∧marginalDensity R θ k≠∞ := by
  obtain ⟨m,hm,hml⟩ := profile_uniform_lower hR.le hθ
  filter_upwards [FiveInvariantFinal.cube_ae_openCube R] with k hk
  have hkc : k∈cube R := fun j=>(hk j).le
  have hn : ¬CollisionFrequency.isCubeCorner R k := fun hc=>(ne_of_lt (hk 0)) (hc 0)
  have hp := CollisionFrequencyPositive.geometricFrequency_noncorner_positive hR hkc hn
  have hl := density_geometric_lower hR.le hm hml k
  refine ⟨ne_of_gt (?_ : 0 < marginalDensity R θ k),marginalDensity_finite hR.le hθ k⟩
  exact (ENNReal.ofReal_pos.mpr (mul_pos (pow_pos hm 4) hp)).trans_le hl

theorem cube_marginal_equivalent {R : ℝ} (hR : 0<R) {θ : Thermodynamics.Parameter}
    (hθ : θ∈Thermodynamics.positiveDomain R) :
    cubeVolume R ≪ marginal R θ ∧ marginal R θ ≪ cubeVolume R := by
  rw [marginal_cube_density hR.le θ]
  exact ⟨withDensity_absolutelyContinuous' (marginalDensity_measurable R θ).aemeasurable
    ((marginalDensity_valid_ae hR hθ).mono (fun _ hp=>hp.1)),
      withDensity_absolutelyContinuous _ _⟩

end
end Resonance.ActualPairNormalization
