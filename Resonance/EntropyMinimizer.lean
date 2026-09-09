import Resonance.Entropy

/-!
Unique minimization by the actual matched RJ state on the sharp cube, for
positive L¹ competitors whose entropy may be infinite. Equality at the minimum
is checked in ENNReal before passing to a.e. equality; no totalized real
integral is used to recognize zero entropy.
-/
namespace Resonance.EntropyMinimizer

open MeasureTheory
open Resonance.Entropy
open scoped ENNReal

theorem extendedEntropy_eq_zero_iff
    {α : Type*} [MeasurableSpace α] {μ : Measure α} {f g : α → ℝ}
    (hfm : AEMeasurable f μ) (hgm : AEMeasurable g μ)
    (hf : ∀ᵐ x ∂μ, 0 < f x) (hg : ∀ᵐ x ∂μ, 0 < g x) :
    extendedEntropy μ f g = 0 ↔ f =ᵐ[μ] g := by
  rw [extendedEntropy, lintegral_eq_zero_iff' (aemeasurable_density hfm hgm).ennreal_ofReal]
  constructor
  · intro hz
    filter_upwards [hf, hg, hz] with x hfx hgx hx
    have hle : density (f x) (g x) ≤ 0 := ENNReal.ofReal_eq_zero.mp hx
    exact (density_eq_zero_iff hfx hgx).mp (le_antisymm hle (density_nonneg hfx hgx))
  · intro he
    filter_upwards [hf, hg, he] with x hfx hgx hx
    rw [(density_eq_zero_iff hfx hgx).mpr hx]
    simp

theorem cube_rj_pos_ae (R : ℝ) (θ : Fin 5 → ℝ)
    (hθ : ∀ k ∈ sharpCube R, 0 < denominator fiveInvariants θ k) :
    ∀ᵐ k ∂cubeMeasure R, 0 < rj fiveInvariants θ k := by
  filter_upwards [cube_denominator_pos_ae R θ hθ] with k hk
  exact inv_pos.mpr hk

theorem cube_rj_density_integrable (R : ℝ) (θ β : Fin 5 → ℝ)
    (hθ : ∀ k ∈ sharpCube R, 0 < denominator fiveInvariants θ k)
    (hβ : ∀ k ∈ sharpCube R, 0 < denominator fiveInvariants β k) :
    Integrable (fun k => density (rj fiveInvariants θ k) (rj fiveInvariants β k))
      (cubeMeasure R) := by
  letI := cube_finite R
  apply integrable_density (cube_rj_pos_ae R θ hθ) (cube_rj_pos_ae R β hβ)
  · simpa only [rj, div_inv_eq_mul] using integrable_mul_denominator fiveInvariants β
      (cube_rj_moment_integrable R θ hθ)
  · exact cube_rj_log_integrable R θ hθ
  · exact cube_rj_log_integrable R β hβ

theorem cube_rj_extendedEntropy_ne_top (R : ℝ) (θ β : Fin 5 → ℝ)
    (hθ : ∀ k ∈ sharpCube R, 0 < denominator fiveInvariants θ k)
    (hβ : ∀ k ∈ sharpCube R, 0 < denominator fiveInvariants β k) :
    extendedEntropy (cubeMeasure R) (rj fiveInvariants θ) (rj fiveInvariants β) ≠ ∞ := by
  rw [extendedEntropy_eq_ofReal_entropy (cube_rj_pos_ae R θ hθ) (cube_rj_pos_ae R β hβ)
    (cube_rj_density_integrable R θ β hθ hβ)]
  exact ENNReal.ofReal_ne_top

/-- All positive L¹ competitors with the actual five moments are admitted,
including competitors of infinite relative entropy. The equality case is
exactly equality to the original RJ function almost everywhere. -/
theorem cube_matched_rj_unique_minimum (R : ℝ) (θ β : Fin 5 → ℝ)
    {f : (Fin 3 → ℝ) → ℝ}
    (hθ : ∀ k ∈ sharpCube R, 0 < denominator fiveInvariants θ k)
    (hβ : ∀ k ∈ sharpCube R, 0 < denominator fiveInvariants β k)
    (hfpos : ∀ᵐ k ∂cubeMeasure R, 0 < f k)
    (hf : Integrable f (cubeMeasure R))
    (hmatch : ∀ i : Fin 5, moment (cubeMeasure R) fiveInvariants f i =
      moment (cubeMeasure R) fiveInvariants (rj fiveInvariants θ) i) :
    extendedEntropy (cubeMeasure R) (rj fiveInvariants θ) (rj fiveInvariants β) ≤
      extendedEntropy (cubeMeasure R) f (rj fiveInvariants β) ∧
    (extendedEntropy (cubeMeasure R) f (rj fiveInvariants β) =
      extendedEntropy (cubeMeasure R) (rj fiveInvariants θ) (rj fiveInvariants β) ↔
      f =ᵐ[cubeMeasure R] rj fiveInvariants θ) := by
  have hp := cube_entropy_pythagoras_extended R θ β hθ hβ hfpos hf hmatch
  constructor
  · rw [hp]
    exact le_add_self
  · rw [hp]
    have hfinite := cube_rj_extendedEntropy_ne_top R θ β hθ hβ
    have hcancel :
        (extendedEntropy (cubeMeasure R) f (rj fiveInvariants θ) +
          extendedEntropy (cubeMeasure R) (rj fiveInvariants θ) (rj fiveInvariants β) =
          extendedEntropy (cubeMeasure R) (rj fiveInvariants θ) (rj fiveInvariants β)) ↔
        extendedEntropy (cubeMeasure R) f (rj fiveInvariants θ) = 0 := by
      simpa only [add_comm, add_zero, zero_add] using
        (ENNReal.add_right_inj (b := extendedEntropy (cubeMeasure R) f (rj fiveInvariants θ))
          (c := 0) hfinite)
    rw [hcancel]
    exact extendedEntropy_eq_zero_iff hf.aestronglyMeasurable.aemeasurable
      (aemeasurable_denominator (fun i => (fiveInvariants_continuous i).measurable.aemeasurable) θ).inv
      hfpos (cube_rj_pos_ae R θ hθ)

end Resonance.EntropyMinimizer
