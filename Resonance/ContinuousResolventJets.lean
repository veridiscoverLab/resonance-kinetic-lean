import Resonance.ContinuousResolventSmooth
import Resonance.RegularizedParameterJets

/-! Uniform parameter jets of the actual C(D) resolvent. Smoothness is
proved in C(D) first; the isometric ambient embedding then transfers the
already proved uniform L∞ estimates, including the weighted 1/s bound. -/
open Set MeasureTheory
open scoped ContDiff Topology
namespace Resonance.ContinuousResolventJets
noncomputable section
set_option maxHeartbeats 2400000
open ResonantMeasure Thermodynamics ContinuousResolventSmooth
open CubeLinftyCoordinates CubeContinuousEssentialNorm RegularizedParameterJets

abbrev CX (R : ℝ) := C(cube R,ℝ)
abbrev LX (R : ℝ) := LinftyMultiplication.X R

def embedOps {R : ℝ} (hR : 0<R) :
    (CX R→L[ℝ]CX R)→ₗᵢ[ℝ](CX R→L[ℝ]LX R) := (embedIsometry hR).postcomp

def restrictOps (R : ℝ) : (LX R→L[ℝ]LX R)→L[ℝ](CX R→L[ℝ]LX R) :=
  (ContinuousLinearMap.compL ℝ (CX R) (LX R) (LX R)).flip (embed R)

theorem embed_bound (R : ℝ) : ‖embed R‖≤1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro f
  simpa only [one_mul] using extendVector_bound R f

theorem restrictOps_bound (R : ℝ) : ‖restrictOps R‖≤1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro T
  exact (ContinuousLinearMap.opNorm_comp_le T (embed R)).trans
    ((mul_le_mul_of_nonneg_left (embed_bound R) (norm_nonneg T)).trans_eq (by ring))

theorem inverse_embed {R : ℝ} (hR : 0<R) {θ : Parameter}
    (hθ : θ∈positiveDomain R) (s : ℝ) (hs : 1 ≤ s) :
    embedOps hR (inverseFamily hR s θ)=restrictOps R (boundedMap hR θ s hs) := by
  apply ContinuousLinearMap.ext
  intro F
  change embed R (inverseFamily hR s θ F)=boundedMap hR θ s hs (embed R F)
  rw [actual_continuous_inverse_apply hR hθ (zero_lt_one.trans_le hs),
    ContinuousRegularizedEquation.output_embed,boundedMap_eq hR hθ]

def weightedFamily {R : ℝ} (hR : 0<R) (s : ℝ) (θ : Parameter) : CX R→L[ℝ]CX R :=
  (RegularizedGraphNorm.weightMap hR.le).comp (inverseFamily hR s θ)

theorem weightedFamily_contDiffAt {R : ℝ} (hR : 0<R) {θ : Parameter}
    (hθ : θ∈positiveDomain R) {s : ℝ} (hs : 0<s) :
    ContDiffAt ℝ ∞ (weightedFamily hR s) θ :=
  contDiffAt_const.clm_comp (actual_continuous_inverse_contDiffAt hR hθ hs)

theorem weighted_embed {R : ℝ} (hR : 0<R) {θ : Parameter}
    (hθ : θ∈positiveDomain R) (s : ℝ) (hs : 1 ≤ s) :
    embedOps hR (weightedFamily hR s θ)=restrictOps R (weightedMap hR θ s hs) := by
  apply ContinuousLinearMap.ext
  intro F
  apply MeasureTheory.Lp.ext
  have he := congrArg (fun T : CX R→L[ℝ]LX R=>T F) (inverse_embed hR hθ s hs)
  change embed R (inverseFamily hR s θ F)=boundedMap hR θ s hs (embed R F) at he
  have hp := (embed_ae R (inverseFamily hR s θ F)).symm
  rw [he] at hp
  filter_upwards [embed_ae R (weightedFamily hR s θ F),hp,
    boundedMap_same_physical hR hθ s hs (embed R F),
    weightedMap_same_physical hR hθ s hs (embed R F),
    ae_restrict_mem (measurable_cube R)] with k hw hf hb hv hk
  change embed R (weightedFamily hR s θ F) k=weightedMap hR θ s hs (embed R F) k
  rw [hw,hv,zeroExtension_apply R _ ⟨k,hk⟩]
  rw [zeroExtension_apply R _ ⟨k,hk⟩] at hf
  change CollisionFrequency.referenceFrequency R k*inverseFamily hR s θ F ⟨k,hk⟩=_
  rw [hf,hb]

theorem isometric_jet_transfer {Y Z W : Type*}
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    (E : Y→ₗᵢ[ℝ]Z) (L : W→L[ℝ]Z) (hL : ‖L‖≤1)
    {f : Parameter→Y} {g : Parameter→W} {θ : Parameter}
    (hf : ContDiffAt ℝ ∞ f θ) (hg : ContDiffAt ℝ ∞ g θ)
    (he : (fun β=>E (f β))=ᶠ[𝓝 θ](fun β=>L (g β))) (n : ℕ) :
    ‖iteratedFDeriv ℝ n f θ‖≤‖iteratedFDeriv ℝ n g θ‖ := by
  have hn : (n : WithTop ℕ∞)≤∞ := by
    exact_mod_cast (show (n:ℕ∞)≤⊤ from le_top)
  have hd := (he.iteratedFDeriv ℝ n).eq_of_nhds
  calc
    _ = ‖iteratedFDeriv ℝ n (E.toContinuousLinearMap ∘ f) θ‖ := by
      rw [E.toContinuousLinearMap.iteratedFDeriv_comp_left hf hn,
        E.norm_compContinuousMultilinearMap]
    _ = ‖iteratedFDeriv ℝ n (L ∘ g) θ‖ := congrArg norm hd
    _ ≤ ‖L‖*‖iteratedFDeriv ℝ n g θ‖ := L.norm_iteratedFDeriv_comp_left hg hn
    _ ≤ _ := (mul_le_mul_of_nonneg_right hL (norm_nonneg _)).trans_eq (one_mul _)

theorem actual_continuous_resolvent_parameter_jets {R : ℝ} (hR : 0<R)
    {K : Set Parameter} (hK : IsCompact K) (hpos : K⊆positiveDomain R) (n : ℕ) :
    ∃C : ℝ,0<C ∧ ∀θ∈K,∀(s : ℝ)(_hs : 1 ≤ s),
      ‖iteratedFDeriv ℝ n (inverseFamily hR s) θ‖≤C ∧
      ‖iteratedFDeriv ℝ n (weightedFamily hR s) θ‖≤C/s := by
  obtain ⟨C,hC,hb⟩ := actual_regularized_parameter_jets hR hK hpos n
  refine ⟨C,hC,?_⟩
  intro θ hθ s hs
  have hs0 : 0<s := zero_lt_one.trans_le hs
  have hn := (positiveDomain_isOpen R).eventually_mem (hpos hθ)
  have hbs : ContDiffAt ℝ ∞ (fun β=>boundedMap hR β s hs) θ :=
    (UniformShiftSpace.evalMap R (inverseShift s hs)).contDiff.contDiffAt.comp θ
      (UniformResolventJets.boundedFamily_contDiffAt hR (hpos hθ))
  have hws : ContDiffAt ℝ ∞ (fun β=>weightedMap hR β s hs) θ :=
    ((UniformShiftSpace.evalMap R (inverseShift s hs)).contDiff.contDiffAt.comp θ
      (UniformResolventSmooth.weightedCellFamily_contDiffAt hR (hpos hθ))).const_smul s⁻¹
  constructor
  · apply le_trans (isometric_jet_transfer (embedOps hR) (restrictOps R) (restrictOps_bound R)
      (actual_continuous_inverse_contDiffAt hR (hpos hθ) hs0) hbs ?_ n) (hb θ hθ s hs).1
    filter_upwards [hn] with β hβ
    exact inverse_embed hR hβ s hs
  · apply le_trans (isometric_jet_transfer (embedOps hR) (restrictOps R) (restrictOps_bound R)
      (weightedFamily_contDiffAt hR (hpos hθ) hs0) hws ?_ n) (hb θ hθ s hs).2.1
    filter_upwards [hn] with β hβ
    exact weighted_embed hR hβ s hs

end
end Resonance.ContinuousResolventJets
