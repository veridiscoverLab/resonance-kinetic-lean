import Resonance.Thermodynamics
import Resonance.JointMultiplier

/-!
The actual Rayleigh--Jeans four-leg weight on the same concrete pairing measure.
The denominator is the original five-moment denominator, composed with the
Euclidean coordinate map. No independent legs or abstract positive weight are
substituted. Identification of the base measure with the physical coarea measure
remains a separate theorem. No collision coercivity or PDE limit is assumed here.
-/
namespace Resonance.WeightedJointMeasure

open MeasureTheory Filter
open MeasureTheory.Measure
open scoped Topology ENNReal BigOperators
open Resonance.ResonantMeasure
open Resonance.Thermodynamics

noncomputable section

def coordinates (k : E) : Fin 3 → ℝ := fun j => k j

theorem coordinates_continuous : Continuous coordinates := by
  apply continuous_pi
  intro j
  change Continuous (fun k : E => k j)
  fun_prop

theorem coordinates_cube (R : ℝ) (k : E) :
    k ∈ cube R ↔ coordinates k ∈ Resonance.Entropy.sharpCube R := by
  constructor
  · intro hk
    exact ⟨fun j => (abs_le.mp (hk j)).1, fun j => (abs_le.mp (hk j)).2⟩
  · intro hk j
    exact abs_le.mpr ⟨hk.1 j, hk.2 j⟩

def profile (θ : Parameter) (k : E) : ℝ :=
  Resonance.Entropy.rj Resonance.Entropy.fiveInvariants θ (coordinates k)

theorem profile_measurable (θ : Parameter) : Measurable (profile θ) := by
  exact ((Resonance.Entropy.cube_denominator_continuous θ).measurable.comp
    coordinates_continuous.measurable).inv

theorem profile_pos {R : ℝ} {θ : Parameter} (hθ : θ ∈ positiveDomain R)
    {k : E} (hk : k ∈ cube R) : 0 < profile θ k := by
  exact inv_pos.mpr (hθ (coordinates k) ((coordinates_cube R k).mp hk))

theorem profile_bounded {R : ℝ} {θ : Parameter} (hθ : θ ∈ positiveDomain R) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ k ∈ cube R, |profile θ k| ≤ C := by
  obtain ⟨C, hC⟩ := (isCompact_Icc : IsCompact (Resonance.Entropy.sharpCube R)).bddAbove_image
    (Resonance.Entropy.cube_rj_continuousOn R θ hθ).norm
  refine ⟨max C 0, le_max_right _ _, ?_⟩
  intro k hk
  exact (hC ⟨coordinates k, (coordinates_cube R k).mp hk, rfl⟩).trans (le_max_left _ _)

def weight (θ : Parameter) (k : FourMomenta) : ℝ≥0∞ :=
  ENNReal.ofReal (∏ i : Fin 4, profile θ (k i))

theorem weight_measurable (θ : Parameter) : Measurable (weight θ) := by
  exact (Finset.measurable_prod Finset.univ
    (fun i _ => (profile_measurable θ).comp (measurable_pi_apply i))).ennreal_ofReal

def jointMeasure (R : ℝ) (θ : Parameter) : Measure FourMomenta :=
  (pairingMeasure R).withDensity (weight θ)

theorem joint_absolutelyContinuous (R : ℝ) (θ : Parameter) :
    jointMeasure R θ ≪ pairingMeasure R := withDensity_absolutelyContinuous _ _

theorem weight_pos_ae {R : ℝ} {θ : Parameter} (hθ : θ ∈ positiveDomain R) :
    ∀ᵐ k ∂pairingMeasure R, 0 < weight θ k := by
  filter_upwards [ae_iff.mpr (pairing_supported_on_fullResonance R)] with k hk
  exact ENNReal.ofReal_pos.mpr (Finset.prod_pos (fun i _ => profile_pos hθ (hk.1 i)))

theorem pairing_absolutelyContinuous {R : ℝ} {θ : Parameter}
    (hθ : θ ∈ positiveDomain R) : pairingMeasure R ≪ jointMeasure R θ :=
  withDensity_absolutelyContinuous' (weight_measurable θ).aemeasurable
    ((weight_pos_ae hθ).mono (fun _ hk => ne_of_gt hk))

theorem positive_parameters_equivalent {R : ℝ} {θ β : Parameter}
    (hθ : θ ∈ positiveDomain R) (hβ : β ∈ positiveDomain R) :
    jointMeasure R θ ≪ jointMeasure R β ∧ jointMeasure R β ≪ jointMeasure R θ :=
  ⟨(joint_absolutelyContinuous R θ).trans (pairing_absolutelyContinuous hβ),
   (joint_absolutelyContinuous R β).trans (pairing_absolutelyContinuous hθ)⟩

theorem jointMeasure_finite {R : ℝ} (hR : 0 ≤ R) {θ : Parameter}
    (hθ : θ ∈ positiveDomain R) : IsFiniteMeasure (jointMeasure R θ) := by
  letI : IsFiniteMeasure (pairingMeasure R) := pairingMeasure_finite hR
  obtain ⟨C, hC, hbound⟩ := profile_bounded hθ
  apply isFiniteMeasure_withDensity
  apply ne_of_lt
  calc
    (∫⁻ k, weight θ k ∂pairingMeasure R) ≤
        ∫⁻ _, ENNReal.ofReal (C ^ 4) ∂pairingMeasure R := by
      apply lintegral_mono_ae
      filter_upwards [ae_iff.mpr (pairing_supported_on_fullResonance R)] with k hk
      apply ENNReal.ofReal_le_ofReal
      calc
        (∏ i : Fin 4, profile θ (k i)) ≤ ∏ _i : Fin 4, C := by
          apply Finset.prod_le_prod
          · intro i _
            exact (profile_pos hθ (hk.1 i)).le
          · intro i _
            exact (le_abs_self _).trans (hbound (k i) (hk.1 i))
        _ = C ^ 4 := by simp
    _ < ∞ := by
      rw [lintegral_const]
      exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (measure_lt_top _ _)

theorem jointMeasure_positive {R : ℝ} (hR : 0 < R) {θ : Parameter}
    (hθ : θ ∈ positiveDomain R) : 0 < jointMeasure R θ Set.univ := by
  by_contra hn
  have hz : jointMeasure R θ Set.univ = 0 := le_antisymm (le_of_not_gt hn) (zero_le _)
  have hp := pairing_absolutelyContinuous hθ hz
  exact (ne_of_gt (pairingMeasure_positive hR)) hp

theorem weight_incoming (θ : Parameter) (k : FourMomenta) :
    weight θ (swapIncomingK k) = weight θ k := by
  simp [weight, swapIncomingK, Fin.prod_univ_succ]
  congr 1
  ring

theorem weight_outgoing (θ : Parameter) (k : FourMomenta) :
    weight θ (swapOutgoingK k) = weight θ k := by
  simp [weight, swapOutgoingK, Fin.prod_univ_succ]
  congr 1
  ring

theorem weight_pairs (θ : Parameter) (k : FourMomenta) :
    weight θ (swapPairsK k) = weight θ k := by
  simp [weight, swapPairsK, Fin.prod_univ_succ]
  congr 1
  ring

theorem preserving_withDensity {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {T : α → α} (hT : MeasurePreserving T μ μ)
    {w : α → ℝ≥0∞} (hw : Measurable w) (hinv : ∀ x, w (T x) = w x) :
    MeasurePreserving T (μ.withDensity w) (μ.withDensity w) := by
  refine ⟨hT.measurable, ?_⟩
  apply Measure.ext
  intro s hs
  rw [Measure.map_apply hT.measurable hs, withDensity_apply _ (hT.measurable hs),
    withDensity_apply _ hs]
  have h := hT.setLIntegral_comp_preimage hs hw
  simpa only [hinv] using h

theorem incoming_preserves_joint (R : ℝ) (θ : Parameter) :
    MeasurePreserving swapIncomingK (jointMeasure R θ) (jointMeasure R θ) :=
  preserving_withDensity (incoming_preserves_pairing R) (weight_measurable θ)
    (weight_incoming θ)

theorem outgoing_preserves_joint (R : ℝ) (θ : Parameter) :
    MeasurePreserving swapOutgoingK (jointMeasure R θ) (jointMeasure R θ) :=
  preserving_withDensity (outgoing_preserves_pairing R) (weight_measurable θ)
    (weight_outgoing θ)

theorem pairs_preserves_joint (R : ℝ) (θ : Parameter) :
    MeasurePreserving swapPairsK (jointMeasure R θ) (jointMeasure R θ) :=
  preserving_withDensity (pairs_preserves_pairing R) (weight_measurable θ)
    (weight_pairs θ)

theorem leg_quasiMeasurePreserving_cube (R : ℝ) (θ : Parameter) (i : Fin 4) :
    QuasiMeasurePreserving (fun k : FourMomenta => k i) (jointMeasure R θ)
      (volume.restrict (cube R)) :=
  (Resonance.JointMultiplier.leg_quasiMeasurePreserving_cube R i).mono_left
    (joint_absolutelyContinuous R θ)

theorem marginal_absolutelyContinuous_cube (R : ℝ) (θ : Parameter) (i : Fin 4) :
    Measure.map (fun k : FourMomenta => k i) (jointMeasure R θ) ≪
      volume.restrict (cube R) :=
  (leg_quasiMeasurePreserving_cube R θ i).absolutelyContinuous

theorem joint_supported_on_fullResonance (R : ℝ) (θ : Parameter) :
    jointMeasure R θ (fullResonance R)ᶜ = 0 :=
  joint_absolutelyContinuous R θ (pairing_supported_on_fullResonance R)

theorem marginal_via_joint_symmetry (R : ℝ) (θ : Parameter)
    (S : FourMomenta → FourMomenta)
    (hS : MeasurePreserving S (jointMeasure R θ) (jointMeasure R θ))
    (i j : Fin 4) (hij : ∀ k, S k i = k j) :
    Measure.map (fun k : FourMomenta => k j) (jointMeasure R θ) =
      Measure.map (fun k : FourMomenta => k i) (jointMeasure R θ) := by
  have he : (fun k : FourMomenta => k j) = (fun k => k i) ∘ S :=
    funext (fun k => (hij k).symm)
  rw [he, ← Measure.map_map (measurable_pi_apply i) hS.measurable, hS.map_eq]

theorem marginal_eq_first (R : ℝ) (θ : Parameter) (i : Fin 4) :
    Measure.map (fun k : FourMomenta => k i) (jointMeasure R θ) =
      Measure.map (fun k : FourMomenta => k 0) (jointMeasure R θ) := by
  fin_cases i
  · rfl
  · exact marginal_via_joint_symmetry R θ swapIncomingK (incoming_preserves_joint R θ)
      0 1 (fun k => rfl)
  · exact marginal_via_joint_symmetry R θ swapPairsK (pairs_preserves_joint R θ)
      0 2 (fun k => rfl)
  · exact (marginal_via_joint_symmetry R θ swapPairsK (pairs_preserves_joint R θ)
      1 3 (fun k => rfl)).trans
      (marginal_via_joint_symmetry R θ swapIncomingK (incoming_preserves_joint R θ)
      0 1 (fun k => rfl))

theorem leg_tendstoInMeasure {R : ℝ} (hR : 0 ≤ R) {θ : Parameter}
    (hθ : θ ∈ positiveDomain R)
    {ι : Type*} {l : Filter ι} [l.IsCountablyGenerated]
    (i : Fin 4) {b : ι → E → ℝ} {c : E → ℝ}
    (hb : ∀ n, AEStronglyMeasurable (b n) (volume.restrict (cube R)))
    (hconv : TendstoInMeasure (volume.restrict (cube R)) b l c) :
    TendstoInMeasure (jointMeasure R θ) (fun n k => b n (k i)) l (fun k => c (k i)) := by
  letI : IsFiniteMeasure (jointMeasure R θ) := jointMeasure_finite hR hθ
  exact Resonance.JointMultiplier.pullback_tendstoInMeasure
    (leg_quasiMeasurePreserving_cube R θ i) hb hconv

set_option maxHeartbeats 800000 in
/-- The fixed test may depend on the whole weighted quartet. Only cube-a.e.
data are assumed for the one-leg multiplier. -/
theorem joint_leg_multiplier_strong {R : ℝ} (hR : 0 ≤ R) {θ : Parameter}
    (hθ : θ ∈ positiveDomain R)
    {ι F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    {l : Filter ι} [l.IsCountablyGenerated] (i : Fin 4)
    {b : ι → E → ℝ} {c : E → ℝ} {V : FourMomenta → F} {C : ℝ}
    (hb : ∀ n, AEStronglyMeasurable (b n) (volume.restrict (cube R)))
    (hc : AEStronglyMeasurable c (volume.restrict (cube R)))
    (hbnd : ∀ n, ∀ᵐ x ∂volume.restrict (cube R), |b n x| ≤ C)
    (hcnd : ∀ᵐ x ∂volume.restrict (cube R), |c x| ≤ C)
    (hconv : TendstoInMeasure (volume.restrict (cube R)) b l c)
    (hV : MemLp V 2 (jointMeasure R θ)) :
    ∃ G : ι → Lp F 2 (jointMeasure R θ),
      (∀ n, G n =ᵐ[jointMeasure R θ] (fun k => (b n (k i)-c (k i)) • V k)) ∧
      Tendsto G l (𝓝 0) := by
  have hT := leg_quasiMeasurePreserving_cube R θ i
  exact Resonance.FixedMultiplier.fixed_multiplier_strong
    (μ := jointMeasure R θ) (σ := jointMeasure R θ)
    (Measure.AbsolutelyContinuous.refl _) (leg_tendstoInMeasure hR hθ i hb hconv)
    (fun n => (hb n).comp_quasiMeasurePreserving hT)
    (hc.comp_quasiMeasurePreserving hT)
    (fun n => hT.ae (hbnd n)) (hT.ae hcnd) hV

set_option maxHeartbeats 800000 in
/-- The complete square-root mobility multiplier acts strongly on an arbitrary
fixed test of this same RJ-weighted quartet, using only cube-a.e. data. -/
theorem quartetRoot_fixed_test_strong {R : ℝ} (hR : 0 ≤ R) (θ : Parameter)
    {ι F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    {l : Filter ι} [l.IsCountablyGenerated]
    {b : ι → E → ℝ} {c : E → ℝ} {V : FourMomenta → F} {C : ℝ}
    (hb : ∀ n, AEStronglyMeasurable (b n) (volume.restrict (cube R)))
    (hc : AEStronglyMeasurable c (volume.restrict (cube R)))
    (hbnd : ∀ n, ∀ᵐ x ∂volume.restrict (cube R), |b n x| ≤ C)
    (hcnd : ∀ᵐ x ∂volume.restrict (cube R), |c x| ≤ C)
    (hconv : TendstoInMeasure (volume.restrict (cube R)) b l c)
    (hV : MemLp V 2 (jointMeasure R θ)) :
    ∃ G : ι → Lp F 2 (jointMeasure R θ),
      (∀ n, G n =ᵐ[jointMeasure R θ] (fun k =>
        (Resonance.JointMultiplier.quartetRoot (b n) k -
          Resonance.JointMultiplier.quartetRoot c k) • V k)) ∧
      Tendsto G l (𝓝 0) := by
  have hac := joint_absolutelyContinuous R θ
  exact Resonance.FixedMultiplier.fixed_multiplier_strong
    (μ := pairingMeasure R) (σ := jointMeasure R θ) hac
    (Resonance.JointMultiplier.quartetRoot_tendstoInMeasure hR hb hconv)
    (fun n => AEStronglyMeasurable.mono_ac hac
      (Resonance.JointMultiplier.quartetRoot_measurable R (hb n)))
    (AEStronglyMeasurable.mono_ac hac
      (Resonance.JointMultiplier.quartetRoot_measurable R hc))
    (fun n => hac.ae_le (Resonance.JointMultiplier.quartetRoot_bound R (hbnd n)))
    (hac.ae_le (Resonance.JointMultiplier.quartetRoot_bound R hcnd)) hV

end
end Resonance.WeightedJointMeasure
