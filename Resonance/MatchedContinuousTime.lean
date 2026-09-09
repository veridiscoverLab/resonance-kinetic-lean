import Resonance.MatchedMomentEquation
import Resonance.WithinEvaluationDerivative

/-! Supremum-norm time derivatives of the actual matched field on its original
moment-image window. Only the physical C(phase) derivative is required. -/
open Set MeasureTheory
open scoped BigOperators
namespace Resonance.MatchedContinuousTime
noncomputable section
open FreeTransport JetCollision SpatialChainRule SpatialJetSpace
open ContinuousCollisionMoments JetMomentDynamics ActualMatchedMoments
open Thermodynamics ThermodynamicChart TransportMaterialDerivative
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 30000

theorem actualMoments_continuous (R : ℝ) : Continuous (actualMoments R) := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  exact (moments R).continuous.comp
    ((ContinuousMap.continuous_curry.comp continuous_fst).eval continuous_snd)

theorem advection_continuous (R : ℝ) : Continuous (advection R) := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  have hA : Continuous (fun z : Space R × Phase R => z.1.val.2.1 z.2.1) := by
    exact (((continuous_subtype_val.comp continuous_fst).snd.fst).eval continuous_snd.fst)
  have hv : Continuous (fun z : Space R × Phase R => velocity R z.2.2) := by
    unfold velocity
    apply continuous_pi
    intro j
    fun_prop
  exact (hA.clm_apply hv).eval continuous_snd.snd

def rateField (R : ℝ) (hR : 0<R) (f d : Distribution R)
    (hf : ∀ X,actualMoments R f X∈momentImage R) : C(SpatialTorus,Parameter) :=
  ⟨fun X => fderiv ℝ (momentInverse R hR) (actualMoments R f X) (actualMoments R d X),by
    have hi : ContinuousOn (fderiv ℝ (momentInverse R hR)) (momentImage R) :=
      (momentInverse_contDiffOn R hR).continuousOn_fderiv_of_isOpen (momentImage_isOpen R hR) le_rfl
    exact (hi.comp_continuous (actualMoments R f).continuous hf).clm_apply
      (actualMoments R d).continuous⟩

def parameterPath (R : ℝ) (hR : 0<R) (s : Set ℝ) (f : ℝ→Distribution R)
    (himage : ∀ t∈s,∀ X,actualMoments R (f t) X∈momentImage R) (t : ℝ) : C(SpatialTorus,Parameter) := by
  classical
  exact if ht : t∈s then matchedField R hR (f t) (himage t ht) else 0

def parameterRatePath (R : ℝ) (hR : 0<R) (s : Set ℝ) (f d : ℝ→Distribution R)
    (himage : ∀ t∈s,∀ X,actualMoments R (f t) X∈momentImage R) (t : ℝ) : C(SpatialTorus,Parameter) := by
  classical
  exact if ht : t∈s then rateField R hR (f t) (d t) (himage t ht) else 0

theorem parameterPath_apply (R : ℝ) (hR : 0<R) (s : Set ℝ) (f : ℝ→Distribution R)
    (himage : ∀ t∈s,∀ X,actualMoments R (f t) X∈momentImage R) {t : ℝ} (ht : t∈s)
    (X : SpatialTorus) :
    parameterPath R hR s f himage t X=matchedValue R hR (f t) X := by
  simp only [parameterPath,dif_pos ht]
  rfl

theorem parameterRatePath_apply (R : ℝ) (hR : 0<R) (s : Set ℝ) (f d : ℝ→Distribution R)
    (himage : ∀ t∈s,∀ X,actualMoments R (f t) X∈momentImage R) {t : ℝ} (ht : t∈s)
    (X : SpatialTorus) :
    parameterRatePath R hR s f d himage t X=
      fderiv ℝ (momentInverse R hR) (actualMoments R (f t) X) (actualMoments R (d t) X) := by
  simp only [parameterRatePath,dif_pos ht]
  rfl

theorem moment_joint_continuousOn (R : ℝ) {s : Set ℝ} {f : ℝ→Distribution R}
    (hf : ContinuousOn f s) :
    ContinuousOn (fun z : ℝ×SpatialTorus => actualMoments R (f z.1) z.2) (s×ˢuniv) :=
  (((actualMoments_continuous R).comp_continuousOn hf).comp continuous_fst.continuousOn
    (fun _ hz => hz.1)).eval continuous_snd.continuousOn

theorem parameterPath_continuousOn (R : ℝ) (hR : 0<R) (s : Set ℝ) (f : ℝ→Distribution R)
    (himage : ∀ t∈s,∀ X,actualMoments R (f t) X∈momentImage R) (hf : ContinuousOn f s) :
    ContinuousOn (parameterPath R hR s f himage) s := by
  apply ContinuousMap.continuousOn_of_continuousOn_uncurry
  have h := (momentInverse_contDiffOn R hR).continuousOn.comp (moment_joint_continuousOn R hf)
    (fun z hz => himage z.1 hz.1 z.2)
  exact h.congr (fun z hz => parameterPath_apply R hR s f himage hz.1 z.2)

theorem parameterRatePath_continuousOn (R : ℝ) (hR : 0<R) (s : Set ℝ) (f d : ℝ→Distribution R)
    (himage : ∀ t∈s,∀ X,actualMoments R (f t) X∈momentImage R)
    (hf : ContinuousOn f s) (hd : ContinuousOn d s) :
    ContinuousOn (parameterRatePath R hR s f d himage) s := by
  apply ContinuousMap.continuousOn_of_continuousOn_uncurry
  have hi := (momentInverse_contDiffOn R hR).continuousOn_fderiv_of_isOpen
    (momentImage_isOpen R hR) le_rfl
  have h := (hi.comp (moment_joint_continuousOn R hf)
    (fun z hz => himage z.1 hz.1 z.2)).clm_apply (moment_joint_continuousOn R hd)
  exact h.congr (fun z hz => parameterRatePath_apply R hR s f d himage hz.1 z.2)

theorem actualMoments_hasDerivWithinAt (R : ℝ) {s : Set ℝ} {f : ℝ→Distribution R}
    {d : Distribution R} {t : ℝ} (hf : HasDerivWithinAt f d s t) (X : SpatialTorus) :
    HasDerivWithinAt (fun τ => actualMoments R (f τ) X) (actualMoments R d X) s t := by
  apply hasDerivWithinAt_pi.mpr
  intro i
  exact (ContinuousMap.evalCLM (R := ℝ) X).hasFDerivAt.comp_hasDerivWithinAt t
    ((spatialMoment R (basisParameter i)).hasFDerivAt.comp_hasDerivWithinAt t hf)

theorem parameterPath_hasDerivWithinAt (R : ℝ) (hR : 0<R) (s : Set ℝ) (hs : Convex ℝ s)
    (f d : ℝ→Distribution R)
    (himage : ∀ t∈s,∀ X,actualMoments R (f t) X∈momentImage R)
    (hf : ContinuousOn f s) (hd : ContinuousOn d s)
    (hder : ∀ t∈s,HasDerivWithinAt f (d t) s t) {t : ℝ} (ht : t∈s) :
    HasDerivWithinAt (parameterPath R hR s f himage)
      (parameterRatePath R hR s f d himage t) s t := by
  apply WithinEvaluationDerivative.hasDerivWithinAt_of_evaluations hs ht
    (parameterRatePath_continuousOn R hR s f d himage hf hd t ht)
  intro τ hτ X
  have h := (momentInverse_hasFDerivAt R hR _ (himage τ hτ X)).differentiableAt.hasFDerivAt.comp_hasDerivWithinAt τ
    (actualMoments_hasDerivWithinAt R (hder τ hτ) X)
  rw [parameterRatePath_apply R hR s f d himage hτ X]
  exact h.congr_of_mem (fun u hu => parameterPath_apply R hR s f himage hu X) hτ

/-- The matched parameter is strongly differentiable in C(T³), using the
same original mild solution. No time derivative in the C³ jet space is asked. -/
theorem original_mild_matched_strong_derivative {R T : ℝ} (hR : 0<R) (hT : 0≤T)
    (c : ℝ) (p₀ : Space R) (p : ℝ→Space R) (hp : ContinuousOn p (Icc 0 T))
    (he : ∀ t∈Icc 0 T,readback (p t)=transport R t (readback p₀)+
      ∫ s in (0 : ℝ)..t,c • transport R (t-s)
        (SpatialCollision.collision R hR.le (readback (p s))))
    (himage : ∀ t∈Icc 0 T,∀ X,actualMoments R (readback (p t)) X∈momentImage R)
    {t : ℝ} (ht : t∈Icc 0 T) :
    HasDerivWithinAt (parameterPath R hR (Icc 0 T) (fun τ => readback (p τ)) himage)
      (parameterRatePath R hR (Icc 0 T) (fun τ => readback (p τ))
        (fun τ => c • SpatialCollision.collision R hR.le (readback (p τ))-advection R (p τ))
        himage t) (Icc 0 T) t := by
  have hf := (readback_continuous R).comp_continuousOn hp
  apply parameterPath_hasDerivWithinAt R hR (Icc 0 T) (convex_Icc 0 T) _ _ himage hf
  · exact (((SpatialCollision.collision_continuous hR.le).comp_continuousOn hf).const_smul c).sub
      ((advection_continuous R).comp_continuousOn hp)
  · intro τ hτ
    exact original_mild_readback_derivative hR.le hT c p₀ p hp he hτ
  · exact ht

#check actualMoments_continuous
#check advection_continuous
#check parameterPath_apply
#check parameterRatePath_apply
#check moment_joint_continuousOn
#check parameterPath_continuousOn
#check parameterRatePath_continuousOn
#check actualMoments_hasDerivWithinAt
#check parameterPath_hasDerivWithinAt
#check original_mild_matched_strong_derivative
#print axioms actualMoments_continuous
#print axioms advection_continuous
#print axioms parameterPath_apply
#print axioms parameterRatePath_apply
#print axioms moment_joint_continuousOn
#print axioms parameterPath_continuousOn
#print axioms parameterRatePath_continuousOn
#print axioms actualMoments_hasDerivWithinAt
#print axioms parameterPath_hasDerivWithinAt
#print axioms original_mild_matched_strong_derivative

end
end Resonance.MatchedContinuousTime
