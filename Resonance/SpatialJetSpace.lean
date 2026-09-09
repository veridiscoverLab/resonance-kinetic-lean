import Resonance.SpatialChainRule
import Mathlib.Analysis.Calculus.UniformLimitsDeriv

/-! A closed Banach space of compatible continuous spatial jets.  Compatibility
means actual Fréchet derivatives on the single real lift of the original torus.
No momentum derivative, Sobolev estimate, or PDE propagation is asserted here. -/
open Set Filter Function
open scoped Topology ContDiff
namespace Resonance.SpatialJetSpace
noncomputable section
set_option maxHeartbeats 1200000
set_option synthInstance.maxHeartbeats 200000
open FreeTransport SpatialChainRule CollisionMultilinear

section Field
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

def fieldLift (f : C(SpatialTorus,F)) : RealPosition → F := f ∘ torusQuotient

omit [NormedSpace ℝ F] in
theorem fieldLift_continuous (f : C(SpatialTorus,F)) : Continuous (fieldLift f) :=
  f.continuous.comp torusQuotient_continuous

def fieldDerivativeGraph : Set (C(SpatialTorus,F) × C(SpatialTorus,RealPosition →L[ℝ] F)) :=
  {p | ∀ x,HasFDerivAt (fieldLift p.1) (p.2 (torusQuotient x)) x}

/-- Uniform convergence of both continuous fields preserves the true derivative. -/
theorem fieldDerivativeGraph_isClosed : IsClosed (fieldDerivativeGraph (F := F)) := by
  apply IsSeqClosed.isClosed
  intro u p hu ht
  have h0 : Tendsto (fun n => (u n).1) atTop (𝓝 p.1) :=
    continuous_fst.continuousAt.tendsto.comp ht
  have h1 : Tendsto (fun n => (u n).2) atTop (𝓝 p.2) :=
    continuous_snd.continuousAt.tendsto.comp ht
  have hu0 := (ContinuousMap.tendsto_iff_tendstoUniformly.mp h0).comp torusQuotient
  have hu1 := (ContinuousMap.tendsto_iff_tendstoUniformly.mp h1).comp torusQuotient
  intro x
  exact hasFDerivAt_of_tendstoUniformly hu1 (fun n y => hu n y)
    (fun y => hu0.tendsto_at y) x

theorem torusQuotient_surjective : Function.Surjective torusQuotient := by
  intro x
  have h : ∀ j : Fin 3,∃ y : ℝ,(y : AddCircle period)=x j :=
    fun j => QuotientAddGroup.mk_surjective (x j)
  choose y hy using h
  exact ⟨y,funext hy⟩

theorem fieldDerivativeGraph_unique {f : C(SpatialTorus,F)}
    {g h : C(SpatialTorus,RealPosition →L[ℝ] F)}
    (hg : (f,g)∈fieldDerivativeGraph) (hh : (f,h)∈fieldDerivativeGraph) : g=h := by
  apply ContinuousMap.ext
  intro x
  obtain ⟨y,rfl⟩ := torusQuotient_surjective x
  exact (hg y).unique (hh y)

end Field

abbrev V0 (R : ℝ) := CubeFunction R
instance v0Normed (R : ℝ) : NormedAddCommGroup (V0 R) := inferInstanceAs (NormedAddCommGroup (CubeFunction R))
instance v0Space (R : ℝ) : NormedSpace ℝ (V0 R) := inferInstanceAs (NormedSpace ℝ (CubeFunction R))
instance v0Complete (R : ℝ) : CompleteSpace (V0 R) := inferInstanceAs (CompleteSpace (CubeFunction R))
abbrev V1 (R : ℝ) := RealPosition →L[ℝ] V0 R
instance v1Normed (R : ℝ) : NormedAddCommGroup (V1 R) :=
  inferInstanceAs (NormedAddCommGroup (RealPosition →L[ℝ] V0 R))
instance v1Space (R : ℝ) : NormedSpace ℝ (V1 R) :=
  inferInstanceAs (NormedSpace ℝ (RealPosition →L[ℝ] V0 R))
instance v1Complete (R : ℝ) : CompleteSpace (V1 R) :=
  inferInstanceAs (CompleteSpace (RealPosition →L[ℝ] V0 R))
abbrev V2 (R : ℝ) := RealPosition →L[ℝ] V1 R
instance v2Normed (R : ℝ) : NormedAddCommGroup (V2 R) :=
  inferInstanceAs (NormedAddCommGroup (RealPosition →L[ℝ] V1 R))
instance v2Space (R : ℝ) : NormedSpace ℝ (V2 R) :=
  inferInstanceAs (NormedSpace ℝ (RealPosition →L[ℝ] V1 R))
instance v2Complete (R : ℝ) : CompleteSpace (V2 R) :=
  inferInstanceAs (CompleteSpace (RealPosition →L[ℝ] V1 R))
abbrev V3 (R : ℝ) := RealPosition →L[ℝ] V2 R
instance v3Normed (R : ℝ) : NormedAddCommGroup (V3 R) :=
  inferInstanceAs (NormedAddCommGroup (RealPosition →L[ℝ] V2 R))
instance v3Space (R : ℝ) : NormedSpace ℝ (V3 R) :=
  inferInstanceAs (NormedSpace ℝ (RealPosition →L[ℝ] V2 R))
instance v3Complete (R : ℝ) : CompleteSpace (V3 R) :=
  inferInstanceAs (CompleteSpace (RealPosition →L[ℝ] V2 R))
abbrev JetData (R : ℝ) := C(SpatialTorus,V0 R) ×
  (C(SpatialTorus,V1 R) × (C(SpatialTorus,V2 R) × C(SpatialTorus,V3 R)))

-- Cache the canonical inherited structures to avoid repeatedly unfolding the
-- three nested operator spaces during elaboration. No new norms are chosen.
instance field0Normed (R : ℝ) : NormedAddCommGroup C(SpatialTorus,V0 R) := inferInstance
instance field1Normed (R : ℝ) : NormedAddCommGroup C(SpatialTorus,V1 R) := inferInstance
instance field2Normed (R : ℝ) : NormedAddCommGroup C(SpatialTorus,V2 R) := inferInstance
instance field3Normed (R : ℝ) : NormedAddCommGroup C(SpatialTorus,V3 R) := inferInstance
instance jetDataNormed (R : ℝ) : NormedAddCommGroup (JetData R) := inferInstance
instance jetDataSpace (R : ℝ) : NormedSpace ℝ (JetData R) := inferInstance
instance field0Complete (R : ℝ) : CompleteSpace C(SpatialTorus,V0 R) := inferInstance
instance field1Complete (R : ℝ) : CompleteSpace C(SpatialTorus,V1 R) := inferInstance
instance field2Complete (R : ℝ) : CompleteSpace C(SpatialTorus,V2 R) := inferInstance
instance field3Complete (R : ℝ) : CompleteSpace C(SpatialTorus,V3 R) := inferInstance
instance jetDataComplete (R : ℝ) : CompleteSpace (JetData R) := inferInstance

def compatible (R : ℝ) : Set (JetData R) :=
  {p | (p.1,p.2.1)∈fieldDerivativeGraph ∧
    (p.2.1,p.2.2.1)∈fieldDerivativeGraph ∧ (p.2.2.1,p.2.2.2)∈fieldDerivativeGraph}

theorem compatible_isClosed (R : ℝ) : IsClosed (compatible R) := by
  change IsClosed ((fun p : JetData R => (p.1,p.2.1)) ⁻¹' fieldDerivativeGraph ∩
    ((fun p : JetData R => (p.2.1,p.2.2.1)) ⁻¹' fieldDerivativeGraph ∩
      (fun p : JetData R => (p.2.2.1,p.2.2.2)) ⁻¹' fieldDerivativeGraph))
  exact (fieldDerivativeGraph_isClosed.preimage (by fun_prop)).inter
    ((fieldDerivativeGraph_isClosed.preimage (by fun_prop)).inter
      (fieldDerivativeGraph_isClosed.preimage (by fun_prop)))

def jetSubmodule (R : ℝ) : Submodule ℝ (JetData R) where
  carrier := compatible R
  zero_mem' := by
    refine ⟨?_,?_,?_⟩ <;> intro x <;> exact hasFDerivAt_const 0 x
  add_mem' := by
    intro p q hp hq
    exact ⟨fun x => (hp.1 x).add (hq.1 x),
      fun x => (hp.2.1 x).add (hq.2.1 x),fun x => (hp.2.2 x).add (hq.2.2 x)⟩
  smul_mem' := by
    intro a p hp
    exact ⟨fun x => (hp.1 x).const_smul a,
      fun x => (hp.2.1 x).const_smul a,fun x => (hp.2.2 x).const_smul a⟩

abbrev JetSpace (R : ℝ) := jetSubmodule R

instance jetSpaceNormed (R : ℝ) : NormedAddCommGroup (JetSpace R) := inferInstance
instance jetSpaceSpace (R : ℝ) : NormedSpace ℝ (JetSpace R) := inferInstance
instance jetSpaceComplete (R : ℝ) : CompleteSpace (JetSpace R) :=
  (compatible_isClosed R).completeSpace_coe

/-- The four fields are actual successive derivatives; continuity of the top
field therefore gives genuine third-order spatial regularity. -/
theorem compatible_contDiff {R : ℝ} {p : JetData R} (hp : p∈compatible R) :
    ContDiff ℝ 3 (fieldLift p.1) ∧ ContDiff ℝ 2 (fieldLift p.2.1) ∧
      ContDiff ℝ 1 (fieldLift p.2.2.1) := by
  have h2 : ContDiff ℝ 1 (fieldLift p.2.2.1) :=
    contDiff_one_iff_hasFDerivAt.mpr
      ⟨fieldLift p.2.2.2,fieldLift_continuous _,hp.2.2⟩
  have h1 : ContDiff ℝ 2 (fieldLift p.2.1) :=
    contDiff_succ_iff_hasFDerivAt.mpr ⟨fieldLift p.2.2.1,h2,hp.2.1⟩
  have h0 : ContDiff ℝ 3 (fieldLift p.1) :=
    contDiff_succ_iff_hasFDerivAt.mpr ⟨fieldLift p.2.1,h1,hp.1⟩
  exact ⟨h0,h1,h2⟩

theorem compatible_first_fderiv {R : ℝ} {p : JetData R} (hp : p∈compatible R)
    (x : RealPosition) : fderiv ℝ (fieldLift p.1) x=p.2.1 (torusQuotient x) :=
  (hp.1 x).fderiv

theorem compatible_second_fderiv {R : ℝ} {p : JetData R} (hp : p∈compatible R)
    (x : RealPosition) : fderiv ℝ (fderiv ℝ (fieldLift p.1)) x=p.2.2.1 (torusQuotient x) := by
  have he : fderiv ℝ (fieldLift p.1)=fieldLift p.2.1 := funext (compatible_first_fderiv hp)
  rw [he]
  exact (hp.2.1 x).fderiv

theorem compatible_third_fderiv {R : ℝ} {p : JetData R} (hp : p∈compatible R)
    (x : RealPosition) :
    fderiv ℝ (fderiv ℝ (fderiv ℝ (fieldLift p.1))) x=p.2.2.2 (torusQuotient x) := by
  have he : fderiv ℝ (fderiv ℝ (fieldLift p.1))=fieldLift p.2.2.1 :=
    funext (compatible_second_fderiv hp)
  rw [he]
  exact (hp.2.2 x).fderiv

def toDistribution {R : ℝ} (p : JetSpace R) : Distribution R :=
  ContinuousMap.uncurry p.val.1

theorem toDistribution_apply {R : ℝ} (p : JetSpace R)
    (x : SpatialTorus) (k : MomentumDomain R) : toDistribution p (x,k)=p.val.1 x k := rfl

theorem toDistribution_realLift {R : ℝ} (p : JetSpace R) :
    realLift (toDistribution p)=fieldLift p.val.1 := rfl

theorem toDistribution_contDiff {R : ℝ} (p : JetSpace R) :
    ContDiff ℝ 3 (realLift (toDistribution p)) := by
  rw [toDistribution_realLift]
  exact (compatible_contDiff p.property).1

theorem toDistribution_injective (R : ℝ) :
    Function.Injective (toDistribution (R := R)) := by
  intro p q hpq
  have h0 : p.val.1=q.val.1 := by
    ext x k
    exact congrArg (fun f : Distribution R => f (x,k)) hpq
  have h1 : p.val.2.1=q.val.2.1 := by
    apply fieldDerivativeGraph_unique p.property.1
    rw [h0]
    exact q.property.1
  have h2 : p.val.2.2.1=q.val.2.2.1 := by
    apply fieldDerivativeGraph_unique p.property.2.1
    rw [h1]
    exact q.property.2.1
  have h3 : p.val.2.2.2=q.val.2.2.2 := by
    apply fieldDerivativeGraph_unique p.property.2.2
    rw [h2]
    exact q.property.2.2
  apply Subtype.ext
  exact Prod.ext h0 (Prod.ext h1 (Prod.ext h2 h3))

theorem toDistribution_norm_le {R : ℝ} (p : JetSpace R) :
    ‖toDistribution p‖≤‖p‖ := by
  apply (ContinuousMap.norm_le _ (norm_nonneg p)).mpr
  intro z
  exact ((p.val.1 z.1).norm_coe_le_norm z.2).trans
    ((p.val.1.norm_coe_le_norm z.1).trans (norm_fst_le p.val))

def toDistributionCLM (R : ℝ) : JetSpace R →L[ℝ] Distribution R :=
  (show JetSpace R →ₗ[ℝ] Distribution R from
    { toFun := fun p : JetSpace R => toDistribution p
      map_add' := by intros; ext z; rfl
      map_smul' := by intros; ext z; rfl }).mkContinuous
    1 (fun p : JetSpace R => by
      change ‖toDistribution p‖≤1*‖p‖
      rw [one_mul]
      exact toDistribution_norm_le p)

theorem toDistributionCLM_apply {R : ℝ} (p : JetSpace R) :
    toDistributionCLM R p=toDistribution p := rfl

instance readoutOpNorm (R : ℝ) : Norm (JetSpace R →L[ℝ] Distribution R) :=
  ContinuousLinearMap.hasOpNorm

theorem toDistributionCLM_norm_le (R : ℝ) : ‖toDistributionCLM R‖≤1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro p
  change ‖toDistribution p‖≤1*‖p‖
  rw [one_mul]
  exact toDistribution_norm_le p

theorem jet_actual_derivatives_bound {R : ℝ} (p : JetSpace R) (x : RealPosition) :
    ‖realLift (toDistribution p) x‖≤‖p‖ ∧
    ‖fderiv ℝ (realLift (toDistribution p)) x‖≤‖p‖ ∧
    ‖fderiv ℝ (fderiv ℝ (realLift (toDistribution p))) x‖≤‖p‖ ∧
    ‖fderiv ℝ (fderiv ℝ (fderiv ℝ (realLift (toDistribution p)))) x‖≤‖p‖ := by
  rw [toDistribution_realLift,compatible_first_fderiv p.property,
    compatible_second_fderiv p.property,compatible_third_fderiv p.property]
  exact ⟨(p.val.1.norm_coe_le_norm _).trans (norm_fst_le p.val),
    (p.val.2.1.norm_coe_le_norm _).trans ((norm_fst_le p.val.2).trans (norm_snd_le p.val)),
    (p.val.2.2.1.norm_coe_le_norm _).trans ((norm_fst_le p.val.2.2).trans
      ((norm_snd_le p.val.2).trans (norm_snd_le p.val))),
    (p.val.2.2.2.norm_coe_le_norm _).trans ((norm_snd_le p.val.2.2).trans
      ((norm_snd_le p.val.2).trans (norm_snd_le p.val)))⟩

end
end Resonance.SpatialJetSpace

#check Resonance.SpatialJetSpace.fieldLift_continuous
#check Resonance.SpatialJetSpace.fieldDerivativeGraph_isClosed
#check Resonance.SpatialJetSpace.torusQuotient_surjective
#check Resonance.SpatialJetSpace.fieldDerivativeGraph_unique
#check Resonance.SpatialJetSpace.compatible_isClosed
#check Resonance.SpatialJetSpace.jetSpaceComplete
#check Resonance.SpatialJetSpace.compatible_contDiff
#check Resonance.SpatialJetSpace.compatible_first_fderiv
#check Resonance.SpatialJetSpace.compatible_second_fderiv
#check Resonance.SpatialJetSpace.compatible_third_fderiv
#check Resonance.SpatialJetSpace.toDistribution_apply
#check Resonance.SpatialJetSpace.toDistribution_realLift
#check Resonance.SpatialJetSpace.toDistribution_contDiff
#check Resonance.SpatialJetSpace.toDistribution_injective
#check Resonance.SpatialJetSpace.toDistribution_norm_le
#check Resonance.SpatialJetSpace.toDistributionCLM_apply
#check Resonance.SpatialJetSpace.toDistributionCLM_norm_le
#check Resonance.SpatialJetSpace.jet_actual_derivatives_bound

#print axioms Resonance.SpatialJetSpace.fieldLift_continuous
#print axioms Resonance.SpatialJetSpace.fieldDerivativeGraph_isClosed
#print axioms Resonance.SpatialJetSpace.torusQuotient_surjective
#print axioms Resonance.SpatialJetSpace.fieldDerivativeGraph_unique
#print axioms Resonance.SpatialJetSpace.compatible_isClosed
#print axioms Resonance.SpatialJetSpace.jetSpaceComplete
#print axioms Resonance.SpatialJetSpace.compatible_contDiff
#print axioms Resonance.SpatialJetSpace.compatible_first_fderiv
#print axioms Resonance.SpatialJetSpace.compatible_second_fderiv
#print axioms Resonance.SpatialJetSpace.compatible_third_fderiv
#print axioms Resonance.SpatialJetSpace.toDistribution_apply
#print axioms Resonance.SpatialJetSpace.toDistribution_realLift
#print axioms Resonance.SpatialJetSpace.toDistribution_contDiff
#print axioms Resonance.SpatialJetSpace.toDistribution_injective
#print axioms Resonance.SpatialJetSpace.toDistribution_norm_le
#print axioms Resonance.SpatialJetSpace.toDistributionCLM_apply
#print axioms Resonance.SpatialJetSpace.toDistributionCLM_norm_le
#print axioms Resonance.SpatialJetSpace.jet_actual_derivatives_bound
