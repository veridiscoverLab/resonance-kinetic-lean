import Resonance.WeakCollision

/-! The nonlinear logarithmic entropy production on the original common
four-leg measure. All integrability comes from the physical cube hypotheses;
no evolution, time chain rule, or classification of the zero set is assumed. -/
open MeasureTheory
open scoped ENNReal

namespace Resonance.NonlinearEntropy
noncomputable section
open Collision ResonantMeasure PhysicalMarginal WeakCollision

def productionDensity (f : E → ℝ) (k : FourMomenta) : ℝ :=
  (1 / 4 : ℝ) * mobility (fun i => f (k i)) *
    (delta (fun i => (f (k i))⁻¹)) ^ 2

def production (R : ℝ) (f : E → ℝ) : ℝ :=
  ∫ k, productionDensity f k ∂pairingMeasure R

theorem all_legs_pos_ae {R : ℝ} {f : E → ℝ}
    (hf : ∀ᵐ k ∂physicalMeasure R, 0 < f k) :
    ∀ᵐ k ∂pairingMeasure R, ∀ i, 0 < f (k i) :=
  ae_all_iff.mpr (fun i => (JointMultiplier.leg_quasiMeasurePreserving_cube R i).ae hf)

theorem productionDensity_eq_density_ae {R : ℝ} {f : E → ℝ}
    (hf : ∀ᵐ k ∂physicalMeasure R, 0 < f k) :
    productionDensity f =ᵐ[pairingMeasure R] density f (fun p => (f p)⁻¹) := by
  filter_upwards [all_legs_pos_ae hf] with k hk
  exact (logarithmic_entropy_production _ hk).symm

theorem productionDensity_integrable {R : ℝ} (hR : 0 ≤ R) {f : E → ℝ}
    (hf : MemLp f ∞ (physicalMeasure R))
    (hi : MemLp (fun k => (f k)⁻¹) ∞ (physicalMeasure R))
    (hp : ∀ᵐ k ∂physicalMeasure R, 0 < f k) :
    Integrable (productionDensity f) (pairingMeasure R) :=
  (density_integrable hR hf hi).congr (productionDensity_eq_density_ae hp).symm

theorem productionDensity_nonneg_ae {R : ℝ} {f : E → ℝ}
    (hp : ∀ᵐ k ∂physicalMeasure R, 0 < f k) :
    ∀ᵐ k ∂pairingMeasure R, 0 ≤ productionDensity f k := by
  filter_upwards [all_legs_pos_ae hp] with k hk
  change 0 ≤ (1 / 4 : ℝ) * mobility (fun i => f (k i)) *
    (delta (fun i => (f (k i))⁻¹)) ^ 2
  rw [← logarithmic_entropy_production _ hk]
  exact logarithmic_entropy_production_nonneg _ hk

theorem production_nonneg {R : ℝ} {f : E → ℝ}
    (hp : ∀ᵐ k ∂physicalMeasure R, 0 < f k) : 0 ≤ production R f :=
  integral_nonneg_of_ae (productionDensity_nonneg_ae hp)

theorem production_eq_original {R : ℝ} (hR : 0 ≤ R) {f : E → ℝ}
    (hf : MemLp f ∞ (physicalMeasure R))
    (hi : MemLp (fun k => (f k)⁻¹) ∞ (physicalMeasure R))
    (hp : ∀ᵐ k ∂physicalMeasure R, 0 < f k) :
    production R f = ∫ k, originalDensity f (fun p => (f p)⁻¹) k ∂pairingMeasure R := by
  calc
    production R f = functional R f (fun p => (f p)⁻¹) :=
      integral_congr_ae (productionDensity_eq_density_ae hp)
    _ = _ := functional_eq_original hR hf hi

theorem original_relative_entropy_dissipation {R : ℝ} (hR : 0 ≤ R)
    (θ : Thermodynamics.Parameter) {f : E → ℝ}
    (hf : MemLp f ∞ (physicalMeasure R))
    (hi : MemLp (fun k => (f k)⁻¹) ∞ (physicalMeasure R))
    (hp : ∀ᵐ k ∂physicalMeasure R, 0 < f k) :
    (∫ k, originalDensity f
      (fun p => WeightedPhysicalForm.reciprocalProfile θ p - (f p)⁻¹) k
      ∂pairingMeasure R) = -production R f := by
  have hg : MemLp (fun p => WeightedPhysicalForm.reciprocalProfile θ p - (f p)⁻¹)
      ∞ (physicalMeasure R) :=
    (WeightedPhysicalForm.reciprocalProfile_memLp_top R θ).sub hi
  rw [← functional_eq_original hR hf hg]
  unfold functional production
  rw [← integral_neg]
  apply integral_congr_ae
  filter_upwards [all_legs_pos_ae hp,
    CollisionLinearization.rj_reciprocal_relation_ae R θ] with k hk hq
  have hq' : delta (fun i => WeightedPhysicalForm.reciprocalProfile θ (k i)) = 0 := by
    simpa only [WeightedPhysicalForm.reciprocalProfile_eq_inv] using hq
  have h := relative_entropy_dissipation (fun i => f (k i))
    (fun i => WeightedPhysicalForm.reciprocalProfile θ (k i)) hk hq'
  simpa only [density, productionDensity, neg_mul] using h

theorem productionDensity_eq_zero_iff (f : E → ℝ) (k : FourMomenta)
    (hp : ∀ i, 0 < f (k i)) :
    productionDensity f k = 0 ↔ delta (fun i => (f (k i))⁻¹) = 0 := by
  have hm : 0 < (1 / 4 : ℝ) * mobility (fun i => f (k i)) := by
    dsimp [mobility]
    exact mul_pos (by norm_num) (mul_pos (mul_pos (mul_pos (hp 0) (hp 1)) (hp 2)) (hp 3))
  simp only [productionDensity, mul_eq_zero, ne_of_gt hm, false_or, sq_eq_zero_iff]

/-- Zero entropy production is exactly the original four-leg reciprocal
relation. This does not substitute a finite-dimensional kernel classification. -/
theorem production_eq_zero_iff {R : ℝ} (hR : 0 ≤ R) {f : E → ℝ}
    (hf : MemLp f ∞ (physicalMeasure R))
    (hi : MemLp (fun k => (f k)⁻¹) ∞ (physicalMeasure R))
    (hp : ∀ᵐ k ∂physicalMeasure R, 0 < f k) :
    production R f = 0 ↔
      ∀ᵐ k ∂pairingMeasure R, delta (fun i => (f (k i))⁻¹) = 0 := by
  rw [production, integral_eq_zero_iff_of_nonneg_ae (productionDensity_nonneg_ae hp)
    (productionDensity_integrable hR hf hi hp)]
  constructor
  · intro he
    filter_upwards [he, all_legs_pos_ae hp] with k hk hpk
    exact (productionDensity_eq_zero_iff f k hpk).mp hk
  · intro he
    filter_upwards [he, all_legs_pos_ae hp] with k hk hpk
    exact (productionDensity_eq_zero_iff f k hpk).mpr hk

end
end Resonance.NonlinearEntropy
