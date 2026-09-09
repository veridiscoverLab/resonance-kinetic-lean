import Resonance.ContinuousCollisionInvariants

/-! Common translations of all four legs preserve the original pairing law.
The smaller cube pays the exact boundary margin; the original center measure
is transported jointly and all radius/direction variables are retained. -/
open Set MeasureTheory Filter
open scoped ENNReal

namespace Resonance.CollisionTranslation
noncomputable section
open ResonantMeasure ContinuousCollisionInvariants

def shiftCenter (z : E) (p : Parameters) : Parameters := (p.1-z,p.2)

theorem shiftCenter_measurePreserving (z : E) : MeasurePreserving (shiftCenter z) base base := by
  exact (measurePreserving_sub_right volume z).prod (MeasurePreserving.id _)

theorem paired_shiftCenter (z : E) (p : Parameters) (i : Fin 4) :
    paired (shiftCenter z p) i = paired p i-z := by
  fin_cases i <;> simp [paired, shiftCenter] <;> abel

theorem cube_sub_margin {r R δ : ℝ} (hmargin : r+δ ≤ R) {x z : E}
    (hx : x ∈ cube r) (hz : z ∈ cube δ) : x-z ∈ cube R := by
  intro j
  change |x j-z j| ≤ R
  exact (abs_sub (x j) (z j)).trans ((add_le_add (hx j) (hz j)).trans hmargin)

theorem shiftCenter_allowed {r R δ : ℝ} (hmargin : r+δ ≤ R) {z : E}
    (hz : z ∈ cube δ) {p : Parameters} (hp : p ∈ allowed r) :
    shiftCenter z p ∈ allowed R := by
  intro i
  rw [paired_shiftCenter]
  exact cube_sub_margin hmargin (hp i) hz

theorem invariant_parameter_iff {R : ℝ} {f : E → ℝ} (hfm : Measurable f) :
    invariant R f ↔ ∀ᵐ p ∂base.restrict (allowed R),
      f (paired p 0)+f (paired p 1)=f (paired p 2)+f (paired p 3) := by
  unfold invariant pairingMeasure parameterMeasure
  rw [ae_map_iff continuous_paired.measurable.aemeasurable
    (measurableSet_eq_fun (by fun_prop) (by fun_prop)),
    Measure.ae_ennreal_smul_measure_iff (by norm_num : (2 : ℝ≥0∞) ≠ 0)]

theorem invariant_shift {r R δ : ℝ} (hmargin : r+δ ≤ R) {z : E}
    (hz : z ∈ cube δ) {f : E → ℝ} (hfm : Measurable f) (hf : invariant R f) :
    invariant r (fun x => f (x-z)) := by
  apply (invariant_parameter_iff (f := fun x => f (x-z)) (by fun_prop)).mpr
  have hp := (invariant_parameter_iff hfm).mp hf
  have hall : ∀ᵐ p ∂base, p ∈ allowed R →
      f (paired p 0)+f (paired p 1)=f (paired p 2)+f (paired p 3) :=
    (ae_restrict_iff' (measurable_allowed R)).mp hp
  have ht : ∀ᵐ p ∂base, shiftCenter z p ∈ allowed R →
      f (paired (shiftCenter z p) 0)+f (paired (shiftCenter z p) 1)=
      f (paired (shiftCenter z p) 2)+f (paired (shiftCenter z p) 3) := by
    apply ae_of_ae_map (μ := base) (p := fun p => p ∈ allowed R →
      f (paired p 0)+f (paired p 1)=f (paired p 2)+f (paired p 3))
      (shiftCenter_measurePreserving z).measurable.aemeasurable
    rwa [(shiftCenter_measurePreserving z).map_eq]
  rw [ae_restrict_iff' (measurable_allowed r)]
  filter_upwards [ht] with p hp hpr
  simpa only [paired_shiftCenter] using hp (shiftCenter_allowed hmargin hz hpr)

end
end Resonance.CollisionTranslation
