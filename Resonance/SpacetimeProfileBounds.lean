import Resonance.SpacetimeReference

/-! Actual compact-positive profile bounds on the common phase reference
measure and the common variable-weight quartet measure. -/
open MeasureTheory MeasureTheory.Measure Set Filter
open scoped ENNReal
namespace Resonance.SpacetimeProfileBounds
noncomputable section
open ResonantMeasure Thermodynamics WeightedJointMeasure SpacetimePairing
open SpacetimeReference LpOperators

theorem measure_domination {R : ℝ} (hR : 0≤R) (T : ℝ) {K : Set Parameter}
    (hK : IsCompact K) (hpos : K⊆positiveDomain R) {θ : Base→Parameter}
    (hθ : ∀ᵐz∂baseMeasure T,θ z∈K) :
    ∃C : ℝ≥0∞,C≠∞ ∧ SpacetimeRJMeasure.measure R T θ≤C • SpacetimePairing.jointMeasure R T := by
  obtain ⟨m,M,hm,hM,hb⟩ := JointWeightComparison.compact_profile_bounds hR hK hpos
  refine ⟨ENNReal.ofReal (M^4),ENNReal.ofReal_ne_top,?_⟩
  rw [SpacetimeRJMeasure.measure,←withDensity_const]
  apply withDensity_mono
  filter_upwards [joint_full_support R T,base_property_on_joint R T hθ] with p hp ht
  apply ENNReal.ofReal_le_ofReal
  calc
    (∏i:Fin 4,profile (θ p.1) (p.2 i))≤∏_:Fin 4,M :=
      Finset.prod_le_prod (fun i _=>(profile_pos (hpos ht) (hp.1 i)).le)
        (fun i _=>(hb (θ p.1) ht (p.2 i) (hp.1 i)).2)
    _=M^4 := by simp

def inverseProfile (θ : Base→Parameter) (z : Source) : ℝ := (profile (θ z.1) z.2)⁻¹

theorem inverseProfile_measurable {θ : Base→Parameter} (hm : Measurable θ) :
    Measurable (inverseProfile θ) :=
  (SpacetimeRJMeasure.joint_profile_measurable.comp
    ((hm.comp measurable_fst).prodMk measurable_snd)).inv

theorem inverseProfile_memLp {R : ℝ} (hR : 0≤R) (T : ℝ) {K : Set Parameter}
    (hK : IsCompact K) (hpos : K⊆positiveDomain R) {θ : Base→Parameter}
    (hm : Measurable θ) (hθ : ∀ᵐz∂baseMeasure T,θ z∈K) :
    MemLp (inverseProfile θ) ∞ (reference R T) := by
  obtain ⟨m,M,hm0,hM,hb⟩ := JointWeightComparison.compact_profile_bounds hR hK hpos
  apply memLp_top_of_bound (inverseProfile_measurable hm).aestronglyMeasurable m⁻¹
  have ht : ∀ᵐz∂reference R T,θ z.1∈K := Measure.quasiMeasurePreserving_fst.ae hθ
  have hk : ∀ᵐz∂reference R T,z.2∈cube R :=
    Measure.quasiMeasurePreserving_snd.ae (ReferenceFrequencySpace.reference_support R)
  filter_upwards [ht,hk] with z ht hk
  rw [inverseProfile,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr (profile_pos (hpos ht) hk))]
  exact inv_anti₀ hm0 (hb (θ z.1) ht z.2 hk).1

theorem weighted_leg_reference {R : ℝ} (hR : 0<R) (T : ℝ)
    (θ : Base→Parameter) (i : Fin 4) :
    QuasiMeasurePreserving (leg i) (SpacetimeRJMeasure.measure R T θ) (reference R T) :=
  ⟨(SpacetimeRJMeasure.leg_quasiMeasurePreserving hR.le T θ i).measurable,
    (SpacetimeRJMeasure.leg_quasiMeasurePreserving hR.le T θ i).absolutelyContinuous.trans
      (SpacetimeReference.reference_volume_equivalent hR T).2⟩

end
end Resonance.SpacetimeProfileBounds
