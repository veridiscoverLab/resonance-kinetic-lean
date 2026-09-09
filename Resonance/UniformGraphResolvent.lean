import Resonance.UniformGraphSpace
import Resonance.IsometricRangeSmooth

/-! Smoothness in the common supremum graph space for every real s≥1.
The ambient family is the actual already constructed full L∞ resolvent;
closed isometric range lifting preserves the original continuous fields. -/
open Set
open scoped ENNReal ContDiff Topology
namespace Resonance.UniformGraphResolvent
noncomputable section
set_option maxHeartbeats 2400000
set_option synthInstance.maxHeartbeats 200000
open Thermodynamics UniformGraphSpace GraphResolventJets
open ContinuousResolventSmooth ContinuousResolventJets RegularizedGraphNorm
open CubeLinftyCoordinates UniformResolventJets UniformResolventSmooth

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

local instance familyComplete {R : ℝ} (hR : 0≤R) : CompleteSpace (Space hR) :=
  spaceComplete hR

theorem pointwise_uniform_bound {R : ℝ} (hR : 0<R) {θ : Parameter}
    (hθ : θ∈positiveDomain R) :
    ∃C : ℝ,0<C ∧ ∀s : Index,‖graphFamily hR s θ‖≤C := by
  obtain ⟨C,hC,hb⟩ := ContinuousResolventBounds.actual_graph_resolvent_bound hR
    isCompact_singleton (show ({θ} : Set Parameter)⊆positiveDomain R by simpa)
  refine ⟨C,hC,fun s => ?_⟩
  apply ContinuousLinearMap.opNorm_le_bound _ hC.le
  intro F
  change ‖lift hR.le s (inverseFamily hR s θ F)‖≤_
  rw [actual_continuous_inverse_apply hR hθ
    (zero_lt_one.trans_le s.property)]
  exact hb θ (mem_singleton θ) s s.property F

def bound {R : ℝ} (hR : 0<R) {θ : Parameter} (hθ : θ∈positiveDomain R) : ℝ :=
  (pointwise_uniform_bound hR hθ).choose

def actualOperator {R : ℝ} (hR : 0<R) {θ : Parameter} (hθ : θ∈positiveDomain R) :
    Sources R→L[ℝ]Space hR.le :=
  SupFamilyLinear.diagonal (fun s : Index => graphFamily hR s θ)
    (pointwise_uniform_bound hR hθ).choose_spec.1.le
    (pointwise_uniform_bound hR hθ).choose_spec.2

def resolver {R : ℝ} (hR : 0<R) (θ : Parameter) : Sources R→L[ℝ]Space hR.le :=
  by
    classical
    exact if hθ : θ∈positiveDomain R then actualOperator hR hθ else 0

theorem resolver_apply {R : ℝ} (hR : 0<R) {θ : Parameter}
    (hθ : θ∈positiveDomain R) (F : Sources R) (s : Index) :
    resolver hR θ F s=lift hR.le s (inverseFamily hR s θ (F s)) := by
  simp only [resolver,dif_pos hθ]
  rfl

theorem resolver_ambient {R : ℝ} (hR : 0<R) {θ : Parameter}
    (hθ : θ∈positiveDomain R) :
    (embedFamily hR).toContinuousLinearMap.comp (resolver hR θ)=
      ambientMap R (boundedFamily hR θ,weightedCellFamily hR θ) := by
  apply ContinuousLinearMap.ext
  intro F
  apply lp.ext
  funext s
  change (embed R (resolver hR θ F s).val.1,embed R (resolver hR θ F s).val.2)=_
  rw [resolver_apply hR hθ]
  apply Prod.ext
  · have he := congrArg (fun T : UniformGraphSpace.CX R→L[ℝ]UniformGraphSpace.LX R => T (F s))
      (inverse_embed hR hθ s s.property)
    exact he
  · have he := congrArg (fun T : UniformGraphSpace.CX R→L[ℝ]UniformGraphSpace.LX R => T (F s))
      (weighted_embed hR hθ s s.property)
    change embed R (OneWeightedPairReadout.referenceContinuous hR.le*
      inverseFamily hR s θ (F s))=s.val⁻¹ •
      (weightedCellFamily hR θ (shift s) (embed R (F s))) at he
    change embed R (s.val • (OneWeightedPairReadout.referenceContinuous hR.le*
      inverseFamily hR s θ (F s)))=_
    rw [map_smul,he,smul_smul,mul_inv_cancel₀ (zero_lt_one.trans_le s.property).ne',one_smul]
    rfl

theorem actual_resolver_contDiffOn {R : ℝ} (hR : 0<R) :
    ContDiffOn ℝ ∞ (resolver hR) (positiveDomain R) := by
  apply IsometricRangeSmooth.contDiffOn_infty_of_comp
    (IsometricRangeSmooth.operatorEmbed (E:=Sources R) (embedFamily hR))
    (positiveDomain_isOpen R)
  have hb : ContDiffOn ℝ ∞ (boundedFamily hR) (positiveDomain R) :=
    fun θ hθ => (boundedFamily_contDiffAt hR hθ).contDiffWithinAt
  have hw : ContDiffOn ℝ ∞ (weightedCellFamily hR) (positiveDomain R) :=
    fun θ hθ => (weightedCellFamily_contDiffAt hR hθ).contDiffWithinAt
  have ha : ContDiffOn ℝ ∞
      (fun θ => ambientMap R (boundedFamily hR θ,weightedCellFamily hR θ))
      (positiveDomain R) :=
    (ambientMap R).contDiff.comp_contDiffOn (hb.prodMk hw)
  apply ha.congr
  intro θ hθ
  exact resolver_ambient hR hθ

theorem actual_resolver_contDiffAt {R : ℝ} (hR : 0<R) {θ : Parameter}
    (hθ : θ∈positiveDomain R) : ContDiffAt ℝ ∞ (resolver hR) θ :=
  (actual_resolver_contDiffOn hR θ hθ).contDiffAt ((positiveDomain_isOpen R).mem_nhds hθ)

theorem actual_supremum_resolvent_jets {R : ℝ} (hR : 0<R)
    {K : Set Parameter} (hK : IsCompact K) (hpos : K⊆positiveDomain R) (n : ℕ) :
    ∃C : ℝ,0<C ∧ ∀θ∈K,‖iteratedFDeriv ℝ n (resolver hR) θ‖≤C := by
  have hc : ContinuousOn (fun θ => iteratedFDeriv ℝ n (resolver hR) θ) K := by
    intro θ hθ
    exact ((actual_resolver_contDiffAt hR (hpos hθ)).continuousAt_iteratedFDeriv
      (by exact_mod_cast (show (n : ℕ∞)≤⊤ from le_top))).continuousWithinAt
  obtain ⟨M,hM⟩ := hK.bddAbove_image hc.norm
  refine ⟨max M 0+1,by positivity,?_⟩
  intro θ hθ
  exact (hM ⟨θ,hθ,rfl⟩).trans (by linarith [le_max_left M 0])

end
end Resonance.UniformGraphResolvent
