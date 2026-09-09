import Resonance.PhysicalNonlinear
import Resonance.NonlinearEntropy

/-! Exact balances for the constructed physical collision output: all five
moments, the original Rayleigh--Jeans equilibrium, and nonlinear relative
entropy dissipation. This is a static operator result, not a PDE existence
assumption or a time-dependent entropy chain rule. -/
open MeasureTheory
open scoped ENNReal

namespace Resonance.PhysicalBalance
noncomputable section
open Collision ResonantMeasure PhysicalMarginal PhysicalCollisionForm
open WeakCollision PhysicalNonlinear

theorem physicalMeasure_finite {R : ℝ} (hR : 0 ≤ R) :
    IsFiniteMeasure (physicalMeasure R) := by
  have hs : cube R ⊆ Metric.closedBall (0 : E) (3 * R) := by
    intro k hk
    simpa only [Metric.mem_closedBall, dist_zero_right] using norm_le_three_R hR hk
  have hb : (volume : Measure E) (Metric.closedBall (0 : E) (3 * R)) < ∞ :=
    (isCompact_closedBall (0 : E) (3 * R)).measure_lt_top
  have hf := (measure_mono hs).trans_lt hb
  exact ⟨by simpa only [physicalMeasure, Measure.restrict_apply_univ] using hf⟩

def boundedTest {R : ℝ} (hR : 0 ≤ R) (g : E → ℝ)
    (hg : MemLp g ∞ (physicalMeasure R)) : H R := by
  letI := physicalMeasure_finite hR
  exact (hg.mono_exponent (by simp : (2 : ℝ≥0∞) ≤ ∞)).toLp g

theorem boundedTest_ae {R : ℝ} (hR : 0 ≤ R) (g : E → ℝ)
    (hg : MemLp g ∞ (physicalMeasure R)) : boundedTest hR g hg =ᵐ[physicalMeasure R] g :=
  MemLp.coeFn_toLp _

theorem output_boundedTest_pairing {R : ℝ} (hR : 0 ≤ R) (f g : E → ℝ)
    (hf : MemLp f ∞ (physicalMeasure R)) (hg : MemLp g ∞ (physicalMeasure R)) :
    inner ℝ (boundedTest hR g hg) (output hR f hf) =
      ∫ k, originalDensity f g k ∂pairingMeasure R := by
  rw [output_pairing]
  apply integral_congr_ae
  filter_upwards [(JointMultiplier.leg_quasiMeasurePreserving_cube R 0).ae_eq
    (boundedTest_ae hR g hg)] with k hk
  simp only [Function.comp_def] at hk
  simp only [originalDensity, hk]

theorem original_five_conservation {R : ℝ} (hR : 0 ≤ R) (f : E → ℝ)
    (hf : MemLp f ∞ (physicalMeasure R)) (θ : Thermodynamics.Parameter) :
    (∫ k, originalDensity f (WeightedPhysicalForm.reciprocalProfile θ) k
      ∂pairingMeasure R) = 0 := by
  rw [← functional_eq_original hR hf (WeightedPhysicalForm.reciprocalProfile_memLp_top R θ)]
  apply integral_eq_zero_of_ae
  filter_upwards [CollisionLinearization.rj_reciprocal_relation_ae R θ] with k hk
  have hq : delta (fun i => WeightedPhysicalForm.reciprocalProfile θ (k i)) = 0 := by
    simpa only [WeightedPhysicalForm.reciprocalProfile_eq_inv] using hk
  exact invariant_quarter_pairing _ _ hq

/-- Arbitrary coefficients range over the complete five-moment invariant
space; the balance uses the original collision output and actual cube volume. -/
theorem output_five_conservation {R : ℝ} (hR : 0 ≤ R) (f : E → ℝ)
    (hf : MemLp f ∞ (physicalMeasure R)) (θ : Thermodynamics.Parameter) :
    inner ℝ (boundedTest hR (WeightedPhysicalForm.reciprocalProfile θ)
      (WeightedPhysicalForm.reciprocalProfile_memLp_top R θ)) (output hR f hf) = 0 := by
  rw [output_boundedTest_pairing]
  exact original_five_conservation hR f hf θ

theorem rj_output_zero {R : ℝ} (hR : 0 ≤ R) {θ : Thermodynamics.Parameter}
    (hθ : θ ∈ Thermodynamics.positiveDomain R) :
    output hR (WeightedJointMeasure.profile θ) (profile_memLp_top hθ) = 0 := by
  have hj : jointPolynomial hR (WeightedJointMeasure.profile θ) (profile_memLp_top hθ) = 0 := by
    apply Lp.ext
    filter_upwards [jointPolynomial_ae hR (WeightedJointMeasure.profile θ) (profile_memLp_top hθ),
      CollisionLinearization.rj_collision_equilibrium_ae hθ,
      Lp.coeFn_zero ℝ 2 (pairingMeasure R)] with k hk he hz
    exact hk.trans (he.trans hz.symm)
  simp only [output, hj, map_zero]

theorem output_relative_entropy {R : ℝ} (hR : 0 ≤ R) (θ : Thermodynamics.Parameter)
    (f : E → ℝ) (hf : MemLp f ∞ (physicalMeasure R))
    (hi : MemLp (fun k => (f k)⁻¹) ∞ (physicalMeasure R))
    (hp : ∀ᵐ k ∂physicalMeasure R, 0 < f k) :
    inner ℝ (boundedTest hR
      (fun p => WeightedPhysicalForm.reciprocalProfile θ p - (f p)⁻¹)
      ((WeightedPhysicalForm.reciprocalProfile_memLp_top R θ).sub hi))
      (output hR f hf) = -NonlinearEntropy.production R f := by
  rw [output_boundedTest_pairing]
  exact NonlinearEntropy.original_relative_entropy_dissipation hR θ hf hi hp

end
end Resonance.PhysicalBalance
