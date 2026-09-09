import Resonance.SpacetimeRJMeasure
import Resonance.ReferenceFrequencySpace

/-! The common reference-frequency Hilbert space over the actual time-space
base, and the exact four pullbacks into the one original quartet space. -/
open MeasureTheory MeasureTheory.Measure Set
open scoped ENNReal
namespace Resonance.SpacetimeReference
noncomputable section
open ResonantMeasure SpacetimePairing ReferenceFrequencySpace JointWeightComparison

theorem unit_marginal (R : ℝ) :
    FrequencyWeightedForm.marginal R unitParameter=CollisionForm.marginal R := by
  rw [FrequencyWeightedForm.marginal,unit_joint]
  rfl

theorem reference_finite {R : ℝ} (hR : 0≤R) : IsFiniteMeasure (referenceMeasure R) := by
  letI := pairingMeasure_finite hR
  letI : IsFiniteMeasure (CollisionForm.marginal R) := by
    unfold CollisionForm.marginal
    infer_instance
  refine ⟨lt_of_le_of_lt (reference_le_unit hR Set.univ) ?_⟩
  rw [unit_marginal,Measure.smul_apply,smul_eq_mul]
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (measure_lt_top _ _)

def reference (R T : ℝ) : Measure Source := (baseMeasure T).prod (referenceMeasure R)
def marginal (R T : ℝ) : Measure Source := (baseMeasure T).prod (CollisionForm.marginal R)

theorem reference_volume_equivalent {R : ℝ} (hR : 0<R) (T : ℝ) :
    reference R T≪sourceMeasure R T ∧ sourceMeasure R T≪reference R T := by
  letI := reference_finite hR.le
  have h := ReferenceFrequencySpace.reference_volume_equivalent hR
  exact ⟨(Measure.AbsolutelyContinuous.refl _).prod h.2,
    (Measure.AbsolutelyContinuous.refl _).prod h.1⟩

theorem all_legs_preserve {R : ℝ} (hR : 0≤R) (T : ℝ) (i : Fin 4) :
    MeasurePreserving (leg i) (SpacetimePairing.jointMeasure R T) (marginal R T) := by
  letI := pairingMeasure_finite hR
  exact (MeasurePreserving.id (baseMeasure T)).prod (CollisionForm.all_legs_preserve R i)

theorem product_domination {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    (μ : Measure A) {ν σ : Measure B} [SFinite ν] [SFinite σ] {C : ℝ≥0∞}
    (h : ν≤C • σ) : μ.prod ν≤C • μ.prod σ := by
  apply Measure.le_iff.mpr
  intro S hS
  rw [Measure.prod_apply hS,Measure.smul_apply,smul_eq_mul,Measure.prod_apply hS,
    ←lintegral_const_mul C (measurable_measure_prodMk_left hS)]
  apply lintegral_mono
  intro x
  exact h (Prod.mk x ⁻¹' S)

theorem marginal_le_reference {R : ℝ} (hR : 0≤R) (T : ℝ) :
    marginal R T ≤ inverseLowerFactor R • reference R T := by
  letI := reference_finite hR
  letI := pairingMeasure_finite hR
  letI : IsFiniteMeasure (CollisionForm.marginal R) := by
    unfold CollisionForm.marginal
    infer_instance
  exact product_domination (baseMeasure T) (by simpa only [unit_marginal] using unit_le_reference hR)

abbrev Space (R T : ℝ) := Lp ℝ 2 (reference R T)
abbrev Raw (R T : ℝ) := Lp ℝ 2 (SpacetimePairing.jointMeasure R T)

def pullback {R : ℝ} (hR : 0≤R) (T : ℝ) (i : Fin 4) : Space R T→L[ℝ]Raw R T :=
  (Lp.compMeasurePreservingₗᵢ ℝ (leg i) (all_legs_preserve hR T i)).toContinuousLinearMap.comp
    (LpOperators.changeCLM (inverseLowerFactor_finite R) (marginal_le_reference hR T))

theorem pullback_ae {R : ℝ} (hR : 0≤R) (T : ℝ) (i : Fin 4) (u : Space R T) :
    pullback hR T i u=ᵐ[SpacetimePairing.jointMeasure R T](fun p=>u (leg i p)) := by
  let w := LpOperators.changeMeasure (inverseLowerFactor_finite R) (marginal_le_reference hR T) u
  exact (Lp.coeFn_compMeasurePreserving w (all_legs_preserve hR T i)).trans
    ((all_legs_preserve hR T i).quasiMeasurePreserving.ae_eq
      (LpOperators.changeMeasure_ae (inverseLowerFactor_finite R) (marginal_le_reference hR T) u))

end
end Resonance.SpacetimeReference
