import Resonance.SpatialJetDescent
import Resonance.SpatialCollisionJets
import Mathlib.Analysis.Normed.Operator.Banach

/-! The original collision acts on the actual closed spatial jet space.
The trilinear lift is defined through the same four-parent collision operator;
closed-graph arguments supply its Banach continuity without changing the jet norm. -/
open Set Function Filter
open scoped Topology ContDiff
namespace Resonance.JetCollision
noncomputable section
set_option maxHeartbeats 1200000
set_option synthInstance.maxHeartbeats 30000
open FreeTransport SpatialChainRule SpatialJetSpace SpatialJetDescent
open CollisionMultilinear SpatialCollisionJets CollisionFiber

theorem continuous_linear_of_readout
    {E F Z : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    [TopologicalSpace Z] [T2Space Z]
    (L : E →ₗ[ℝ] F) (j : F → Z) (hj : Continuous j) (hi : Injective j)
    (hL : Continuous (j ∘ L)) : Continuous L := by
  apply L.continuous_of_seq_closed_graph
  intro u x y hu hv
  apply hi
  exact tendsto_nhds_unique (hj.continuousAt.tendsto.comp hv)
    (hL.continuousAt.tendsto.comp hu)

-- A definitional alias with explicitly inherited structures prevents class
-- search from repeatedly expanding the nested closed-submodule carrier.
def Space (R : ℝ) : Type := SpatialJetSpace.JetSpace R
instance spaceNormed (R : ℝ) : NormedAddCommGroup (Space R) := jetSpaceNormed R
instance spaceNormedSpace (R : ℝ) : NormedSpace ℝ (Space R) := jetSpaceSpace R
instance spaceGroup (R : ℝ) : AddCommGroup (Space R) := (spaceNormed R).toAddCommGroup
instance spaceModule (R : ℝ) : Module ℝ (Space R) := (spaceNormedSpace R).toModule
instance spaceComplete (R : ℝ) : CompleteSpace (Space R) := jetSpaceComplete R
instance endoNormed (R : ℝ) : NormedAddCommGroup (Space R →L[ℝ] Space R) := inferInstance
instance endoSpace (R : ℝ) : NormedSpace ℝ (Space R →L[ℝ] Space R) := inferInstance
instance endoComplete (R : ℝ) : CompleteSpace (Space R →L[ℝ] Space R) := inferInstance
instance doubleNormed (R : ℝ) : NormedAddCommGroup (Space R →L[ℝ] (Space R →L[ℝ] Space R)) := inferInstance
instance doubleSpace (R : ℝ) : NormedSpace ℝ (Space R →L[ℝ] (Space R →L[ℝ] Space R)) := inferInstance
instance doubleComplete (R : ℝ) : CompleteSpace (Space R →L[ℝ] (Space R →L[ℝ] Space R)) := inferInstance
local notation "JetSpace" => Space

def readback {R : ℝ} (p : Space R) : Distribution R :=
  SpatialJetSpace.toDistribution (R := R) p
local notation "toDistribution" => readback

theorem readback_injective (R : ℝ) : Function.Injective (readback (R := R)) := by
  intro p q h
  exact SpatialJetSpace.toDistribution_injective R h
local notation "toDistribution_injective" => readback_injective

theorem readback_add {R : ℝ} (a b : JetSpace R) :
    toDistribution (a+b)=toDistribution a+toDistribution b := by ext z; rfl

theorem readback_smul {R : ℝ} (s : ℝ) (a : JetSpace R) :
    toDistribution (s • a)=s • toDistribution a := by ext z; rfl

def output (R : ℝ) (hR : 0 ≤ R) (p : Fin 3 → JetSpace R) : Distribution R :=
  spatialTrilinear R hR (fun i => toDistribution (p i))

theorem output_lift (R : ℝ) (hR : 0 ≤ R) (p : Fin 3 → JetSpace R) :
    realLift (output R hR p)=fun x =>
      collisionTrilinear R hR (fun i => realLift (toDistribution (p i)) x) := by
  funext x
  apply ContinuousMap.ext
  intro k
  rfl

theorem output_contDiff (R : ℝ) (hR : 0 ≤ R) (p : Fin 3 → JetSpace R) :
    ContDiff ℝ 3 (realLift (output R hR p)) := by
  rw [output_lift]
  exact (collisionTrilinear R hR).contDiff.comp (contDiff_pi.mpr
    (fun i => toDistribution_contDiff (p i)))

def triple (R : ℝ) (hR : 0 ≤ R) (p : Fin 3 → JetSpace R) : JetSpace R :=
  jetOfDistribution (output R hR p) (output_contDiff R hR p)

theorem triple_readback (R : ℝ) (hR : 0 ≤ R) (p : Fin 3 → JetSpace R) :
    toDistribution (triple R hR p)=output R hR p := jetOfDistribution_readback _ _

def multilinear (R : ℝ) (hR : 0 ≤ R) :
    MultilinearMap ℝ (fun _ : Fin 3 => JetSpace R) (JetSpace R) where
  toFun := triple R hR
  map_update_add' := by
    intro _ p i a b
    apply toDistribution_injective R
    rw [readback_add]
    rw [triple_readback,triple_readback,triple_readback]
    unfold output
    have he (q : JetSpace R) :
        (fun j => toDistribution (update p i q j))=
          update (fun j => toDistribution (p j)) i (toDistribution q) :=
      Function.comp_update (readback (R := R)) p i q
    rw [he,he,he]
    rw [readback_add,(spatialTrilinear R hR).map_update_add]
  map_update_smul' := by
    intro _ p i a b
    apply toDistribution_injective R
    rw [readback_smul]
    rw [triple_readback,triple_readback]
    unfold output
    have he (q : JetSpace R) :
        (fun j => toDistribution (update p i q j))=
          update (fun j => toDistribution (p j)) i (toDistribution q) :=
      Function.comp_update (readback (R := R)) p i q
    rw [he,he]
    rw [readback_smul,(spatialTrilinear R hR).map_update_smul]

def tripleValue (R : ℝ) (hR : 0 ≤ R) (a b d : JetSpace R) : JetSpace R :=
  multilinear R hR ![a,b,d]

theorem tripleValue_readback (R : ℝ) (hR : 0 ≤ R) (a b d : JetSpace R) :
    toDistribution (tripleValue R hR a b d)=
      spatialTrilinear R hR ![toDistribution a,toDistribution b,toDistribution d] := by
  rw [tripleValue]
  change toDistribution (triple R hR ![a,b,d])=_
  rw [triple_readback]
  rfl

theorem readback_continuous (R : ℝ) : Continuous (readback (R := R)) :=
  (toDistributionCLM R).continuous

theorem tripleValue_readback_continuous (R : ℝ) (hR : 0 ≤ R) :
    Continuous (fun p : JetSpace R × (JetSpace R × JetSpace R) =>
      toDistribution (tripleValue R hR p.1 p.2.1 p.2.2)) := by
  simp_rw [tripleValue_readback]
  apply ((spatialTrilinear R hR).contDiff (n := ⊤)).continuous.comp
  apply continuous_pi
  intro i
  fin_cases i
  · exact (readback_continuous R).comp continuous_fst
  · exact (readback_continuous R).comp continuous_snd.fst
  · exact (readback_continuous R).comp continuous_snd.snd

theorem update_three_zero {A : Type*} (a b d e : A) :
    update ![a,b,d] (0 : Fin 3) e=![e,b,d] := by
  ext i
  fin_cases i <;> simp
theorem update_three_one {A : Type*} (a b d e : A) :
    update ![a,b,d] (1 : Fin 3) e=![a,e,d] := by
  ext i
  fin_cases i <;> simp
theorem update_three_two {A : Type*} (a b d e : A) :
    update ![a,b,d] (2 : Fin 3) e=![a,b,e] := by
  ext i
  fin_cases i <;> simp

def lastLinear (R : ℝ) (hR : 0 ≤ R) (a b : JetSpace R) :
    JetSpace R →ₗ[ℝ] JetSpace R where
  toFun := tripleValue R hR a b
  map_add' d e := by
    simpa only [tripleValue,update_three_two] using (multilinear R hR).map_update_add ![a,b,0] 2 d e
  map_smul' s d := by
    simpa only [tripleValue,update_three_two] using (multilinear R hR).map_update_smul ![a,b,0] 2 s d

def lastCLM (R : ℝ) (hR : 0 ≤ R) (a b : JetSpace R) :
    JetSpace R →L[ℝ] JetSpace R := by
  have hp : Continuous (fun d : JetSpace R => (a,(b,d))) :=
    continuous_const.prodMk (continuous_const.prodMk continuous_id)
  have hc := (tripleValue_readback_continuous R hR).comp hp
  have hc' : Continuous ((readback (R := R)) ∘ (lastLinear R hR a b)) := by
    change Continuous (fun d : JetSpace R => readback (tripleValue R hR a b d))
    exact hc
  exact ⟨lastLinear R hR a b,continuous_linear_of_readout (lastLinear R hR a b)
    (readback (R := R)) (readback_continuous R) (readback_injective R) hc'⟩

def middleLinear (R : ℝ) (hR : 0 ≤ R) (a : JetSpace R) :
    JetSpace R →ₗ[ℝ] (JetSpace R →L[ℝ] JetSpace R) where
  toFun := lastCLM R hR a
  map_add' b e := by
    apply ContinuousLinearMap.ext
    intro d
    change multilinear R hR ![a,b+e,d]=multilinear R hR ![a,b,d]+multilinear R hR ![a,e,d]
    simpa only [update_three_one] using
      (multilinear R hR).map_update_add ![a,0,d] 1 b e
  map_smul' s b := by
    apply ContinuousLinearMap.ext
    intro d
    change multilinear R hR ![a,s • b,d]=s • multilinear R hR ![a,b,d]
    simpa only [update_three_one] using
      (multilinear R hR).map_update_smul ![a,0,d] 1 s b

def middleCLM (R : ℝ) (hR : 0 ≤ R) (a : JetSpace R) :
    JetSpace R →L[ℝ] (JetSpace R →L[ℝ] JetSpace R) := by
  let j : (JetSpace R →L[ℝ] JetSpace R) → (JetSpace R → Distribution R) :=
    fun L d => readback (L d)
  have hj : Continuous j := continuous_pi (fun d => (readback_continuous R).comp
    (ContinuousLinearMap.apply ℝ (JetSpace R) d).continuous)
  have hi : Injective j := by
    intro L M h
    apply ContinuousLinearMap.ext
    intro d
    exact readback_injective R (congrFun h d)
  have hc : Continuous (j ∘ middleLinear R hR a) := by
    apply continuous_pi
    intro d
    have hp : Continuous (fun b : JetSpace R => (a,(b,d))) :=
      continuous_const.prodMk (continuous_id.prodMk continuous_const)
    have hh := (tripleValue_readback_continuous R hR).comp hp
    change Continuous (fun b : JetSpace R => readback (tripleValue R hR a b d))
    exact hh
  exact ⟨middleLinear R hR a,continuous_linear_of_readout (middleLinear R hR a) j hj hi hc⟩

def firstLinear (R : ℝ) (hR : 0 ≤ R) :
    JetSpace R →ₗ[ℝ] (JetSpace R →L[ℝ] (JetSpace R →L[ℝ] JetSpace R)) where
  toFun := middleCLM R hR
  map_add' a e := by
    apply ContinuousLinearMap.ext
    intro b
    apply ContinuousLinearMap.ext
    intro d
    change multilinear R hR ![a+e,b,d]=multilinear R hR ![a,b,d]+multilinear R hR ![e,b,d]
    simpa only [update_three_zero] using
      (multilinear R hR).map_update_add ![0,b,d] 0 a e
  map_smul' s a := by
    apply ContinuousLinearMap.ext
    intro b
    apply ContinuousLinearMap.ext
    intro d
    change multilinear R hR ![s • a,b,d]=s • multilinear R hR ![a,b,d]
    simpa only [update_three_zero] using
      (multilinear R hR).map_update_smul ![0,b,d] 0 s a

def curried (R : ℝ) (hR : 0 ≤ R) :
    JetSpace R →L[ℝ] (JetSpace R →L[ℝ] (JetSpace R →L[ℝ] JetSpace R)) := by
  let j : (JetSpace R →L[ℝ] (JetSpace R →L[ℝ] JetSpace R)) →
      (JetSpace R → JetSpace R → Distribution R) := fun L b d => readback (L b d)
  have hj : Continuous j := by
    apply continuous_pi
    intro b
    apply continuous_pi
    intro d
    exact (readback_continuous R).comp
      ((ContinuousLinearMap.apply ℝ (JetSpace R) d).continuous.comp
        (ContinuousLinearMap.apply ℝ (JetSpace R →L[ℝ] JetSpace R) b).continuous)
  have hi : Injective j := by
    intro L M h
    apply ContinuousLinearMap.ext
    intro b
    apply ContinuousLinearMap.ext
    intro d
    exact readback_injective R (congrFun (congrFun h b) d)
  have hc : Continuous (j ∘ firstLinear R hR) := by
    apply continuous_pi
    intro b
    apply continuous_pi
    intro d
    have hp : Continuous (fun a : JetSpace R => (a,(b,d))) :=
      continuous_id.prodMk (continuous_const.prodMk continuous_const)
    have hh := (tripleValue_readback_continuous R hR).comp hp
    change Continuous (fun a : JetSpace R => readback (tripleValue R hR a b d))
    exact hh
  exact ⟨firstLinear R hR,continuous_linear_of_readout (firstLinear R hR) j hj hi hc⟩

theorem curried_apply (R : ℝ) (hR : 0 ≤ R) (a b d : JetSpace R) :
    curried R hR a b d=tripleValue R hR a b d := rfl

def trilinear (R : ℝ) (hR : 0 ≤ R) :
    ContinuousMultilinearMap ℝ (fun _ : Fin 3 => JetSpace R) (JetSpace R) :=
  { multilinear R hR with
    cont := by
      have he : (multilinear R hR : (Fin 3 → JetSpace R) → JetSpace R)=
          fun p => curried R hR (p 0) (p 1) (p 2) := by
        funext p
        rw [curried_apply]
        change multilinear R hR p=multilinear R hR ![p 0,p 1,p 2]
        congr 1
        ext i
        fin_cases i <;> rfl
      change Continuous (multilinear R hR : (Fin 3 → JetSpace R) → JetSpace R)
      rw [he]
      exact (((curried R hR).continuous.comp (continuous_apply 0)).clm_apply
        (continuous_apply 1)).clm_apply (continuous_apply 2) }

theorem trilinear_readback (R : ℝ) (hR : 0 ≤ R) (p : Fin 3 → JetSpace R) :
    toDistribution (trilinear R hR p)=
      spatialTrilinear R hR (fun i => toDistribution (p i)) := triple_readback R hR p

def collision (R : ℝ) (hR : 0 ≤ R) (p : JetSpace R) : JetSpace R :=
  trilinear R hR (fun _ => p)

theorem collision_readback (R : ℝ) (hR : 0 ≤ R) (p : JetSpace R) :
    toDistribution (collision R hR p)=SpatialCollision.collision R hR (toDistribution p) := by
  rw [collision,trilinear_readback,spatialTrilinear_diagonal]

theorem collision_contDiff (R : ℝ) (hR : 0 ≤ R) (n : WithTop ℕ∞) :
    ContDiff ℝ n (collision R hR) :=
  (trilinear R hR).contDiff.comp (contDiff_pi.mpr (fun _ => contDiff_id))

theorem collision_norm_le (R : ℝ) (hR : 0 ≤ R) (p : JetSpace R) :
    ‖collision R hR p‖≤‖trilinear R hR‖*‖p‖^3 := by
  simpa only [collision,Finset.prod_const,Finset.card_univ,Fintype.card_fin] using
    (trilinear R hR).le_opNorm (fun _ => p)

theorem collision_sub_norm_le {R M : ℝ} (hR : 0 ≤ R) (_hM : 0 ≤ M)
    (p q : JetSpace R) (hp : ‖p‖≤M) (hq : ‖q‖≤M) :
    ‖collision R hR p-collision R hR q‖≤
      (3*‖trilinear R hR‖*M^2)*‖p-q‖ := by
  have h := (trilinear R hR).norm_image_sub_le (fun _ : Fin 3 => p) (fun _ : Fin 3 => q)
  have hsub : ((fun _ : Fin 3 => p)-(fun _ : Fin 3 => q))=(fun _ => p-q) := rfl
  rw [hsub] at h
  have hpconst : ‖fun _ : Fin 3 => p‖=‖p‖ := pi_norm_const p
  have hqconst : ‖fun _ : Fin 3 => q‖=‖q‖ := pi_norm_const q
  have hdconst : ‖fun _ : Fin 3 => p-q‖=‖p-q‖ := pi_norm_const (p-q)
  rw [hpconst,hqconst,hdconst] at h
  simp only [Fintype.card_fin,show 3-1=2 from rfl] at h
  apply h.trans
  calc
    ‖trilinear R hR‖*3*max ‖p‖ ‖q‖^2*‖p-q‖ ≤
        ‖trilinear R hR‖*3*M^2*‖p-q‖ := by gcongr; exact max_le hp hq
    _ = _ := by ring

end
end Resonance.JetCollision

#check Resonance.JetCollision.continuous_linear_of_readout
#check Resonance.JetCollision.readback_injective
#check Resonance.JetCollision.readback_add
#check Resonance.JetCollision.readback_smul
#check Resonance.JetCollision.output_lift
#check Resonance.JetCollision.output_contDiff
#check Resonance.JetCollision.triple_readback
#check Resonance.JetCollision.tripleValue_readback
#check Resonance.JetCollision.readback_continuous
#check Resonance.JetCollision.tripleValue_readback_continuous
#check Resonance.JetCollision.update_three_zero
#check Resonance.JetCollision.update_three_one
#check Resonance.JetCollision.update_three_two
#check Resonance.JetCollision.curried_apply
#check Resonance.JetCollision.trilinear_readback
#check Resonance.JetCollision.collision_readback
#check Resonance.JetCollision.collision_contDiff
#check Resonance.JetCollision.collision_norm_le
#check Resonance.JetCollision.collision_sub_norm_le
#print axioms Resonance.JetCollision.continuous_linear_of_readout
#print axioms Resonance.JetCollision.readback_injective
#print axioms Resonance.JetCollision.readback_add
#print axioms Resonance.JetCollision.readback_smul
#print axioms Resonance.JetCollision.output_lift
#print axioms Resonance.JetCollision.output_contDiff
#print axioms Resonance.JetCollision.triple_readback
#print axioms Resonance.JetCollision.tripleValue_readback
#print axioms Resonance.JetCollision.readback_continuous
#print axioms Resonance.JetCollision.tripleValue_readback_continuous
#print axioms Resonance.JetCollision.update_three_zero
#print axioms Resonance.JetCollision.update_three_one
#print axioms Resonance.JetCollision.update_three_two
#print axioms Resonance.JetCollision.curried_apply
#print axioms Resonance.JetCollision.trilinear_readback
#print axioms Resonance.JetCollision.collision_readback
#print axioms Resonance.JetCollision.collision_contDiff
#print axioms Resonance.JetCollision.collision_norm_le
#print axioms Resonance.JetCollision.collision_sub_norm_le
