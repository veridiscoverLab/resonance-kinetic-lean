import Resonance.SpatialJetSpace
import Mathlib.Topology.Algebra.Group.Quotient

/-! Descent of actual real-coordinate derivatives to the original spatial torus.
This identifies the closed compatible jet space with the original distributions
whose single real lift is C³; no momentum regularity is used. -/
open Set Function Topology
open scoped Topology ContDiff
namespace Resonance.SpatialJetDescent
noncomputable section
set_option maxHeartbeats 1200000
set_option synthInstance.maxHeartbeats 200000
open FreeTransport SpatialChainRule SpatialJetSpace CollisionMultilinear

theorem torusQuotient_add (x y : RealPosition) :
    torusQuotient (x+y)=torusQuotient x+torusQuotient y := by
  ext j
  simp [torusQuotient]

theorem torusQuotient_isQuotientMap : IsQuotientMap torusQuotient := by
  have h : IsOpenQuotientMap torusQuotient :=
    IsOpenQuotientMap.piMap (fun _ : Fin 3 => QuotientAddGroup.isOpenQuotientMap_mk)
  exact h.isQuotientMap

def torusSection (x : SpatialTorus) : RealPosition :=
  Classical.choose (torusQuotient_surjective x)

theorem torusSection_spec (x : SpatialTorus) : torusQuotient (torusSection x)=x :=
  Classical.choose_spec (torusQuotient_surjective x)

def FibreInvariant {F : Type*} (f : RealPosition → F) : Prop :=
  ∀ x y,torusQuotient x=torusQuotient y → f x=f y

theorem fieldLift_invariant {F : Type*} [TopologicalSpace F] (f : C(SpatialTorus,F)) :
    FibreInvariant (f ∘ torusQuotient) := by
  intro x y h
  simp only [comp_apply,h]

section Descent
variable {F : Type*} [TopologicalSpace F]

def descend (f : RealPosition → F) (hc : Continuous f) (hi : FibreInvariant f) :
    C(SpatialTorus,F) where
  toFun x := f (torusSection x)
  continuous_toFun := torusQuotient_isQuotientMap.continuous_iff.mpr (by
    have he : (fun x => f (torusSection x)) ∘ torusQuotient=f := by
      funext x
      exact hi _ _ (torusSection_spec _)
    rw [he]
    exact hc)

theorem descend_lift (f : RealPosition → F) (hc : Continuous f) (hi : FibreInvariant f) :
    (descend f hc hi) ∘ torusQuotient=f := by
  funext x
  exact hi _ _ (torusSection_spec _)

end Descent

theorem fderiv_invariant {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : RealPosition → F} (hi : FibreInvariant f) : FibreInvariant (fderiv ℝ f) := by
  intro x y hxy
  have he : (fun z => f (z+x))=(fun z => f (z+y)) := by
    funext z
    apply hi
    rw [torusQuotient_add,torusQuotient_add,hxy]
  have hd := congrArg (fun g => fderiv ℝ g (0 : RealPosition)) he
  simpa only [fderiv_comp_add_right,zero_add] using hd

def jetOfDistribution {R : ℝ} (f : Distribution R) (hf : ContDiff ℝ 3 (realLift f)) :
    JetSpace R := by
  let u0 : C(SpatialTorus,V0 R) := ContinuousMap.curry f
  let u1 := descend (fderiv ℝ (realLift f))
    (hf.continuous_fderiv (by norm_num)) (fderiv_invariant (fieldLift_invariant u0))
  have h1 : ContDiff ℝ 2 (fderiv ℝ (realLift f)) := hf.fderiv_right (by norm_num)
  let u2 := descend (fderiv ℝ (fderiv ℝ (realLift f)))
    (h1.continuous_fderiv (by norm_num))
    (fderiv_invariant (fderiv_invariant (fieldLift_invariant u0)))
  have h2 : ContDiff ℝ 1 (fderiv ℝ (fderiv ℝ (realLift f))) := h1.fderiv_right (by norm_num)
  let u3 := descend (fderiv ℝ (fderiv ℝ (fderiv ℝ (realLift f))))
    (h2.continuous_fderiv (by norm_num))
    (fderiv_invariant (fderiv_invariant (fderiv_invariant (fieldLift_invariant u0))))
  refine ⟨(u0,u1,u2,u3),?_,?_,?_⟩
  · intro x
    have he : fieldLift u1=fderiv ℝ (realLift f) := descend_lift _ _ _
    change HasFDerivAt (realLift f) (fieldLift u1 x) x
    rw [he]
    exact (hf.differentiable (by norm_num) x).hasFDerivAt
  · intro x
    have he1 : fieldLift u1=fderiv ℝ (realLift f) := descend_lift _ _ _
    have he2 : fieldLift u2=fderiv ℝ (fderiv ℝ (realLift f)) := descend_lift _ _ _
    change HasFDerivAt (fieldLift u1) (fieldLift u2 x) x
    rw [he1,he2]
    exact (h1.differentiable (by norm_num) x).hasFDerivAt
  · intro x
    have he2 : fieldLift u2=fderiv ℝ (fderiv ℝ (realLift f)) := descend_lift _ _ _
    have he3 : fieldLift u3=fderiv ℝ (fderiv ℝ (fderiv ℝ (realLift f))) := descend_lift _ _ _
    change HasFDerivAt (fieldLift u2) (fieldLift u3 x) x
    rw [he2,he3]
    exact (h2.differentiable (by norm_num) x).hasFDerivAt

theorem jetOfDistribution_readback {R : ℝ} (f : Distribution R)
    (hf : ContDiff ℝ 3 (realLift f)) : toDistribution (jetOfDistribution f hf)=f := by
  ext z
  rfl

theorem jetOfDistribution_unique {R : ℝ} (p : JetSpace R) :
    jetOfDistribution (toDistribution p) (toDistribution_contDiff p)=p := by
  apply toDistribution_injective R
  exact jetOfDistribution_readback _ _

theorem distribution_has_jet_iff {R : ℝ} (f : Distribution R) :
    (∃ p : JetSpace R,toDistribution p=f) ↔ ContDiff ℝ 3 (realLift f) := by
  constructor
  · rintro ⟨p,rfl⟩
    exact toDistribution_contDiff p
  · intro hf
    exact ⟨jetOfDistribution f hf,jetOfDistribution_readback f hf⟩

/-- The compatible norm is exactly the supremum of the four actual derivative
norms, expressed without choosing coordinate representatives on the torus. -/
theorem jet_norm_le_iff {R M : ℝ} (hM : 0 ≤ M) (p : JetSpace R) :
    ‖p‖≤M ↔ ∀ x : RealPosition,
      ‖realLift (toDistribution p) x‖≤M ∧
      ‖fderiv ℝ (realLift (toDistribution p)) x‖≤M ∧
      ‖fderiv ℝ (fderiv ℝ (realLift (toDistribution p))) x‖≤M ∧
      ‖fderiv ℝ (fderiv ℝ (fderiv ℝ (realLift (toDistribution p)))) x‖≤M := by
  constructor
  · intro hp x
    obtain ⟨h0,h1,h2,h3⟩ := jet_actual_derivatives_bound p x
    exact ⟨h0.trans hp,h1.trans hp,h2.trans hp,h3.trans hp⟩
  · intro h
    have hb : ∀ X : SpatialTorus,
        ‖p.val.1 X‖≤M ∧ ‖p.val.2.1 X‖≤M ∧ ‖p.val.2.2.1 X‖≤M ∧ ‖p.val.2.2.2 X‖≤M := by
      intro X
      obtain ⟨x,rfl⟩ := torusQuotient_surjective X
      have hx := h x
      rw [toDistribution_realLift,compatible_first_fderiv p.property,
        compatible_second_fderiv p.property,compatible_third_fderiv p.property] at hx
      exact hx
    change max ‖p.val.1‖ (max ‖p.val.2.1‖ (max ‖p.val.2.2.1‖ ‖p.val.2.2.2‖))≤M
    exact max_le ((ContinuousMap.norm_le _ hM).mpr (fun X => (hb X).1))
      (max_le ((ContinuousMap.norm_le _ hM).mpr (fun X => (hb X).2.1))
        (max_le ((ContinuousMap.norm_le _ hM).mpr (fun X => (hb X).2.2.1))
          ((ContinuousMap.norm_le _ hM).mpr (fun X => (hb X).2.2.2))))

end
end Resonance.SpatialJetDescent

#check Resonance.SpatialJetDescent.torusQuotient_add
#check Resonance.SpatialJetDescent.torusQuotient_isQuotientMap
#check Resonance.SpatialJetDescent.torusSection_spec
#check Resonance.SpatialJetDescent.fieldLift_invariant
#check Resonance.SpatialJetDescent.descend_lift
#check Resonance.SpatialJetDescent.fderiv_invariant
#check Resonance.SpatialJetDescent.jetOfDistribution_readback
#check Resonance.SpatialJetDescent.jetOfDistribution_unique
#check Resonance.SpatialJetDescent.distribution_has_jet_iff
#check Resonance.SpatialJetDescent.jet_norm_le_iff
#print axioms Resonance.SpatialJetDescent.torusQuotient_add
#print axioms Resonance.SpatialJetDescent.torusQuotient_isQuotientMap
#print axioms Resonance.SpatialJetDescent.torusSection_spec
#print axioms Resonance.SpatialJetDescent.fieldLift_invariant
#print axioms Resonance.SpatialJetDescent.descend_lift
#print axioms Resonance.SpatialJetDescent.fderiv_invariant
#print axioms Resonance.SpatialJetDescent.jetOfDistribution_readback
#print axioms Resonance.SpatialJetDescent.jetOfDistribution_unique
#print axioms Resonance.SpatialJetDescent.distribution_has_jet_iff
#print axioms Resonance.SpatialJetDescent.jet_norm_le_iff
