import Resonance.GraphResolventSmooth

/-! The actual regularized inverse has uniformly bounded parameter
jets as an operator into the complete two-norm graph B_s, for all s≥1.
The second component is sν_* times the first, at every derivative order. -/
open Set
open scoped ContDiff BigOperators
namespace Resonance.GraphResolventJets
noncomputable section
set_option maxHeartbeats 2200000
set_option synthInstance.maxHeartbeats 200000
open ResonantMeasure Thermodynamics RegularizedGraphNorm GraphResolventSmooth
open ContinuousResolventSmooth ContinuousResolventJets

local instance graphOperatorNormed {R : ℝ} (hR : 0≤R) (s : ℝ) :
    NormedAddCommGroup (X R→L[ℝ]graphSpace hR s) :=
  @ContinuousLinearMap.toNormedAddCommGroup ℝ ℝ (X R) (graphSpace hR s)
    inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance
    (RingHom.id ℝ) inferInstance

local instance graphOperatorSpace {R : ℝ} (hR : 0≤R) (s : ℝ) :
    NormedSpace ℝ (X R→L[ℝ]graphSpace hR s) :=
  @ContinuousLinearMap.toNormedSpace ℝ ℝ (X R) (graphSpace hR s)
    inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance
    (RingHom.id ℝ) inferInstance ℝ inferInstance inferInstance inferInstance

def postLift {R : ℝ} (hR : 0≤R) (s : ℝ) :
    (X R→L[ℝ]X R)→L[ℝ](X R→L[ℝ]graphSpace hR s) :=
  ContinuousLinearMap.compL ℝ (X R) (X R) (graphSpace hR s) (liftMap hR s)

def postWeight {R : ℝ} (hR : 0≤R) : (X R→L[ℝ]X R)→L[ℝ](X R→L[ℝ]X R) :=
  ContinuousLinearMap.compL ℝ (X R) (X R) (X R) (weightMap hR)

def graphFamily {R : ℝ} (hR : 0<R) (s : ℝ) (θ : Parameter) :
    X R→L[ℝ]graphSpace hR.le s := postLift hR.le s (inverseFamily hR s θ)

theorem graphFamily_apply {R : ℝ} (hR : 0<R) (s : ℝ) (θ : Parameter) (F : X R) :
    graphFamily hR s θ F=lift hR.le s (inverseFamily hR s θ F) := rfl

theorem graphFamily_contDiffAt {R : ℝ} (hR : 0<R) {θ : Parameter}
    (hθ : θ∈positiveDomain R) {s : ℝ} (hs : 0<s) :
    ContDiffAt ℝ ∞ (graphFamily hR s) θ :=
  (postLift hR.le s).contDiff.contDiffAt.comp θ
    (actual_continuous_inverse_contDiffAt hR hθ hs)

theorem actual_graph_resolvent_parameter_jets {R : ℝ} (hR : 0<R)
    {K : Set Parameter} (hK : IsCompact K) (hpos : K⊆positiveDomain R) (n : ℕ) :
    ∃C : ℝ,0<C ∧ ∀θ∈K,∀(s : ℝ)(_hs : 1 ≤ s),
      ‖iteratedFDeriv ℝ n (graphFamily hR s) θ‖≤C := by
  obtain ⟨C,hC,hb⟩ := actual_continuous_resolvent_parameter_jets hR hK hpos n
  refine ⟨C,hC,?_⟩
  intro θ hθ s hs
  have hs0 : 0<s := zero_lt_one.trans_le hs
  have hn : (n : WithTop ℕ∞)≤∞ := by exact_mod_cast (show (n:ℕ∞)≤⊤ from le_top)
  have hd := (actual_continuous_inverse_contDiffAt hR (hpos hθ) hs0)
  have he := (postLift hR.le s).iteratedFDeriv_comp_left hd hn
  have hw := (postWeight hR.le).iteratedFDeriv_comp_left hd hn
  change iteratedFDeriv ℝ n (graphFamily hR s) θ=_ at he
  change iteratedFDeriv ℝ n (weightedFamily hR s) θ=_ at hw
  rw [he]
  apply ContinuousMultilinearMap.opNorm_le_bound hC.le
  intro m
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro F
  change ‖lift hR.le s ((iteratedFDeriv ℝ n (inverseFamily hR s) θ m) F)‖≤_
  have h0 : ‖(iteratedFDeriv ℝ n (inverseFamily hR s) θ m) F‖≤
      C*(∏i,‖m i‖)*‖F‖ :=
    ((iteratedFDeriv ℝ n (inverseFamily hR s) θ m).le_opNorm F).trans
      (mul_le_mul_of_nonneg_right
        ((iteratedFDeriv ℝ n (inverseFamily hR s) θ).le_of_opNorm_le (hb θ hθ s hs).1 m)
        (norm_nonneg F))
  have h1 : ‖(iteratedFDeriv ℝ n (weightedFamily hR s) θ m) F‖≤
      (C/s)*(∏i,‖m i‖)*‖F‖ :=
    ((iteratedFDeriv ℝ n (weightedFamily hR s) θ m).le_opNorm F).trans
      (mul_le_mul_of_nonneg_right
        ((iteratedFDeriv ℝ n (weightedFamily hR s) θ).le_of_opNorm_le (hb θ hθ s hs).2 m)
        (norm_nonneg F))
  rw [hw] at h1
  change ‖OneWeightedPairReadout.referenceContinuous hR.le*
    ((iteratedFDeriv ℝ n (inverseFamily hR s) θ m) F)‖≤_ at h1
  exact norm_lift_le hR.le hs0.le _ h0
    ((mul_le_mul_of_nonneg_left h1 hs0.le).trans_eq (by field_simp [hs0.ne']))

end
end Resonance.GraphResolventJets
