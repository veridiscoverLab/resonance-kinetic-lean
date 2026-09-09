import Resonance.SpacetimeRootMultiplier
import Resonance.JointWeightComparison

/-! The actual variable Rayleigh--Jeans joint measure on one original
time-space-quartet space. All four factors use the same parameter theta(t,X),
the same unmodified sharp-cube pairing measure, and the original Haar volume. -/
open MeasureTheory MeasureTheory.Measure Set Filter
open scoped ENNReal Topology
namespace Resonance.SpacetimeRJMeasure
noncomputable section
open ResonantMeasure Thermodynamics WeightedJointMeasure SpacetimePairing

theorem joint_profile_measurable : Measurable (fun p : Parameter×E=>profile p.1 p.2) := by
  have hd : Continuous (fun p : Parameter×E=>
      Entropy.denominator Entropy.fiveInvariants p.1 (coordinates p.2)) :=
    denominator_joint_continuous.comp
      (continuous_fst.prodMk (coordinates_continuous.comp continuous_snd))
  exact hd.measurable.inv

def weight (θ : Base→Parameter) (p : Joint) : ℝ≥0∞ :=
  ENNReal.ofReal (∏i:Fin 4,profile (θ p.1) (p.2 i))

theorem weight_measurable {θ : Base→Parameter} (hθ : Measurable θ) : Measurable (weight θ) := by
  apply Measurable.ennreal_ofReal
  apply Finset.measurable_prod
  intro i _
  exact joint_profile_measurable.comp
    ((hθ.comp measurable_fst).prodMk ((measurable_pi_apply i).comp measurable_snd))

def measure (R T : ℝ) (θ : Base→Parameter) : Measure Joint :=
  (SpacetimePairing.jointMeasure R T).withDensity (weight θ)

theorem measure_absolutelyContinuous (R T : ℝ) (θ : Base→Parameter) :
    measure R T θ≪SpacetimePairing.jointMeasure R T := withDensity_absolutelyContinuous _ _

theorem weight_positive_ae (R T : ℝ) {θ : Base→Parameter}
    (hθ : ∀ᵐz∂baseMeasure T,θ z∈positiveDomain R) :
    ∀ᵐp∂SpacetimePairing.jointMeasure R T,0<weight θ p := by
  filter_upwards [joint_full_support R T,base_property_on_joint R T hθ] with p hp ht
  exact ENNReal.ofReal_pos.mpr (Finset.prod_pos (fun i _=>profile_pos ht (hp.1 i)))

theorem reverse_absolutelyContinuous (R T : ℝ) {θ : Base→Parameter}
    (hm : Measurable θ) (hθ : ∀ᵐz∂baseMeasure T,θ z∈positiveDomain R) :
    SpacetimePairing.jointMeasure R T≪measure R T θ :=
  withDensity_absolutelyContinuous' (weight_measurable hm).aemeasurable
    ((weight_positive_ae R T hθ).mono (fun _ h=>h.ne'))

theorem measure_finite {R : ℝ} (hR : 0≤R) (T : ℝ) {K : Set Parameter}
    (hK : IsCompact K) (hpos : K⊆positiveDomain R) {θ : Base→Parameter}
    (hθ : ∀ᵐz∂baseMeasure T,θ z∈K) : IsFiniteMeasure (measure R T θ) := by
  letI := SpacetimePairing.jointMeasure_finite hR T
  obtain ⟨m,M,hm,hM,hbound⟩ := JointWeightComparison.compact_profile_bounds hR hK hpos
  apply isFiniteMeasure_withDensity
  apply ne_of_lt
  calc
    (∫⁻p,weight θ p∂SpacetimePairing.jointMeasure R T)≤
        ∫⁻_,ENNReal.ofReal (M^4)∂SpacetimePairing.jointMeasure R T := by
      apply lintegral_mono_ae
      filter_upwards [joint_full_support R T,base_property_on_joint R T hθ] with p hp ht
      apply ENNReal.ofReal_le_ofReal
      calc
        (∏i:Fin 4,profile (θ p.1) (p.2 i))≤∏_:Fin 4,M :=
          Finset.prod_le_prod (fun i _=>(profile_pos (hpos ht) (hp.1 i)).le)
            (fun i _=>(hbound (θ p.1) ht (p.2 i) (hp.1 i)).2)
        _=M^4 := by simp
    _<∞ := by
      rw [lintegral_const]
      exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (measure_lt_top _ _)

theorem leg_quasiMeasurePreserving {R : ℝ} (hR : 0≤R) (T : ℝ)
    (θ : Base→Parameter) (i : Fin 4) :
    QuasiMeasurePreserving (leg i) (measure R T θ) (sourceMeasure R T) :=
  ⟨(SpacetimePairing.leg_quasiMeasurePreserving hR T i).measurable,
    ((measure_absolutelyContinuous R T θ).map (SpacetimePairing.leg_quasiMeasurePreserving hR T i).measurable).trans
      (SpacetimePairing.leg_quasiMeasurePreserving hR T i).absolutelyContinuous⟩

theorem incoming_preserves {R : ℝ} (hR : 0≤R) (T : ℝ) {θ : Base→Parameter}
    (hm : Measurable θ) :
    MeasurePreserving (Prod.map id swapIncomingK) (measure R T θ) (measure R T θ) := by
  letI := pairingMeasure_finite hR
  exact preserving_withDensity
    ((MeasurePreserving.id (baseMeasure T)).prod (incoming_preserves_pairing R))
    (weight_measurable hm) (fun p=>weight_incoming (θ p.1) p.2)

theorem outgoing_preserves {R : ℝ} (hR : 0≤R) (T : ℝ) {θ : Base→Parameter}
    (hm : Measurable θ) :
    MeasurePreserving (Prod.map id swapOutgoingK) (measure R T θ) (measure R T θ) := by
  letI := pairingMeasure_finite hR
  exact preserving_withDensity
    ((MeasurePreserving.id (baseMeasure T)).prod (outgoing_preserves_pairing R))
    (weight_measurable hm) (fun p=>weight_outgoing (θ p.1) p.2)

theorem pairs_preserves {R : ℝ} (hR : 0≤R) (T : ℝ) {θ : Base→Parameter}
    (hm : Measurable θ) :
    MeasurePreserving (Prod.map id swapPairsK) (measure R T θ) (measure R T θ) := by
  letI := pairingMeasure_finite hR
  exact preserving_withDensity
    ((MeasurePreserving.id (baseMeasure T)).prod (pairs_preserves_pairing R))
    (weight_measurable hm) (fun p=>weight_pairs (θ p.1) p.2)

theorem whole_root_fixed_test_strong {R : ℝ} (hR : 0≤R) (T : ℝ)
    (θ : Base→Parameter) {ι F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    {l : Filter ι} [l.IsCountablyGenerated] {b : ι→Source→ℝ} {c : Source→ℝ}
    {V : Joint→F} {C : ℝ}
    (hb : ∀n,AEStronglyMeasurable (b n) (sourceMeasure R T))
    (hc : AEStronglyMeasurable c (sourceMeasure R T))
    (hbnd : ∀n,∀ᵐz∂sourceMeasure R T,|b n z|≤C)
    (hcnd : ∀ᵐz∂sourceMeasure R T,|c z|≤C)
    (hconv : TendstoInMeasure (sourceMeasure R T) b l c)
    (hV : MemLp V 2 (measure R T θ)) :
    ∃G:ι→Lp F 2 (measure R T θ),
      (∀n,G n=ᵐ[measure R T θ](fun p=>(SpacetimeRootMultiplier.root (b n) p-
        SpacetimeRootMultiplier.root c p) • V p)) ∧ Tendsto G l (𝓝 0) :=
  SpacetimeRootMultiplier.root_fixed_test_strong hR T
    (measure_absolutelyContinuous R T θ) hb hc hbnd hcnd hconv hV

end
end Resonance.SpacetimeRJMeasure
