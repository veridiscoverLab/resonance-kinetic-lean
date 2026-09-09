import Resonance.MatchedJetStrongTime

/-! Low-order actual coframe jets and their full material derivatives.
The actual matched parameter is never replaced by an independently supplied
macroscopic evolution. -/
open Set Function
open scoped ContDiff
namespace Resonance.ActualCoframeLowTime
noncomputable section
open FreeTransport JetCollision SpatialChainRule SpatialJetSpace JetEnergy
open ActualMatchedMoments Thermodynamics ThermodynamicChart ActualCoframeWeight
open MatchedContinuousTime MatchedLowJetTime MatchedJetStrongTime
open LowSpatialMaterialDerivative TransportMaterialDerivative
set_option maxHeartbeats 1500000

section Actual
variable (R T : ℝ) (hR : 0<R) (p : ℝ→Space R)
  (himage : ∀ τ∈Icc 0 T,∀ X,actualMoments R (readback (p τ)) X∈momentImage R)

abbrev actualQ (t : ℝ) : Space R := coframeJet R hR (Icc 0 T) p himage t

def firstRate (a : RealPosition) (t : ℝ) : Distribution R :=
  denominatorField R (compositionRatePath R hR (firstComposition (momentInverse R hR))
    (firstComposition_contDiffOn R hR) (Icc 0 T) (fun τ => dataField R (p τ) a 0)
    (fun τ => dataRateField R (p τ) a 0) himage t)

def secondRate (a b : RealPosition) (t : ℝ) : Distribution R :=
  denominatorField R (compositionRatePath R hR (secondComposition (momentInverse R hR))
    (secondComposition_contDiffOn R hR) (Icc 0 T) (fun τ => dataField R (p τ) a b)
    (fun τ => dataRateField R (p τ) a b) himage t)

theorem actualQ_ordered_parameter (n : ℕ) (hn : n≤3) (v : Fin n→RealPosition)
    {t : ℝ} (ht : t∈Icc 0 T) (x : RealPosition) (k : MomentumDomain R) :
    spatialDerivative R n hn v (actualQ R T hR p himage t) (torusQuotient x,k)=
      denominatorCube R (iteratedFDeriv ℝ n
        (fun y => matchedValue R hR (readback (p t)) (torusQuotient y)) x v) k := by
  rw [derivative_at_quotient]
  change iteratedFDeriv ℝ n (realLift (readback (coframeJet R hR (Icc 0 T) p himage t))) x v k=_
  rw [coframeJet_readback,denominatorField_realLift]
  have h := (denominatorCube R).iteratedFDeriv_comp_left (x := x)
    (actual_parameterPath_contDiff R hR (Icc 0 T) p himage t).contDiffAt (by exact_mod_cast hn)
  have he : (fun y => parameterPath R hR (Icc 0 T) (fun τ => readback (p τ)) himage t (torusQuotient y))=
      fun y => matchedValue R hR (readback (p t)) (torusQuotient y) :=
    funext (fun y => parameterPath_apply R hR (Icc 0 T) _ himage ht (torusQuotient y))
  have hh := congrArg (fun A => A v k) h
  simp only [Function.comp_def] at hh
  rw [he] at hh
  exact hh

theorem actualQ_first_path (a : RealPosition) {t : ℝ} (ht : t∈Icc 0 T) :
    spatialDerivative R 1 (by omega) ![a] (actualQ R T hR p himage t)=
      denominatorField R (compositionPath R (firstComposition (momentInverse R hR))
        (firstComposition_contDiffOn R hR) (Icc 0 T) (fun τ => dataField R (p τ) a 0) himage t) := by
  ext z
  obtain ⟨x,hx⟩ := torusQuotient_surjective z.1
  have hz : z=(torusQuotient x,z.2) := Prod.ext hx.symm rfl
  rw [hz,actualQ_ordered_parameter R T hR p himage 1 (by omega) ![a] ht x z.2]
  exact congrArg (fun v : Parameter => denominatorCube R v z.2)
    (actual_first_jet_path_value hR p himage a 0 x ht).symm

theorem actualQ_second_path (a b : RealPosition) {t : ℝ} (ht : t∈Icc 0 T) :
    spatialDerivative R 2 (by omega) ![a,b] (actualQ R T hR p himage t)=
      denominatorField R (compositionPath R (secondComposition (momentInverse R hR))
        (secondComposition_contDiffOn R hR) (Icc 0 T) (fun τ => dataField R (p τ) a b) himage t) := by
  ext z
  obtain ⟨x,hx⟩ := torusQuotient_surjective z.1
  have hz : z=(torusQuotient x,z.2) := Prod.ext hx.symm rfl
  rw [hz,actualQ_ordered_parameter R T hR p himage 2 (by omega) ![a,b] ht x z.2]
  exact congrArg (fun v : Parameter => denominatorCube R v z.2)
    (actual_second_jet_path_value hR p himage a b x ht).symm

variable (hT : 0≤T) (c : ℝ) (p₀ : Space R) (hp : ContinuousOn p (Icc 0 T))
  (he : ∀ t∈Icc 0 T,readback (p t)=transport R t (readback p₀)+
    ∫ s in (0:ℝ)..t,c • transport R (t-s)
      (SpatialCollision.collision R hR.le (readback (p s))))
include hp he hT

theorem actualQ_material {t : ℝ} (ht : t∈Icc 0 T) :
    HasDerivWithinAt (fun τ => transport R (-τ) (readback (actualQ R T hR p himage τ)))
      (transport R (-t) (coframeTimeRate R hR (Icc 0 T) c p himage t+
        advection R (actualQ R T hR p himage t))) (Icc 0 T) t :=
  material_readback_hasDerivWithinAt R
    (original_mild_coframe_strong_derivative hR hT c p₀ p hp he himage ht)

theorem actualQ_first_time (a : RealPosition) {t : ℝ} (ht : t∈Icc 0 T) :
    HasDerivWithinAt (fun τ => spatialDerivative R 1 (by omega) ![a] (actualQ R T hR p himage τ))
      (firstRate R T hR p himage a t) (Icc 0 T) t := by
  have h := (denominatorField R).hasFDerivAt.comp_hasDerivWithinAt t
    (actual_first_jet_strong_derivative hR hT c p₀ p hp he himage a 0 ht)
  exact h.congr_of_mem (fun τ hτ => actualQ_first_path R T hR p himage a hτ) ht

theorem actualQ_second_time (a b : RealPosition) {t : ℝ} (ht : t∈Icc 0 T) :
    HasDerivWithinAt (fun τ => spatialDerivative R 2 (by omega) ![a,b] (actualQ R T hR p himage τ))
      (secondRate R T hR p himage a b t) (Icc 0 T) t := by
  have h := (denominatorField R).hasFDerivAt.comp_hasDerivWithinAt t
    (actual_second_jet_strong_derivative hR hT c p₀ p hp he himage a b ht)
  exact h.congr_of_mem (fun τ hτ => actualQ_second_path R T hR p himage a b hτ) ht

theorem actualQ_first_material (a : RealPosition) {t : ℝ} (ht : t∈Icc 0 T) :
    HasDerivWithinAt (fun τ => transport R (-τ)
      (spatialDerivative R 1 (by omega) ![a] (actualQ R T hR p himage τ)))
      (transport R (-t) (firstRate R T hR p himage a t+
        fieldAdvection R (firstDerivativeField R (actualQ R T hR p himage t) a))) (Icc 0 T) t := by
  have hc : Continuous (fun z : ℝ×Distribution R => transportCLM R (-z.1) z.2) :=
    (TransportDuhamel.transport_joint_continuous R).comp (continuous_fst.neg.prodMk continuous_snd)
  have h := strong_family_hasDerivWithinAt (fun τ => transportCLM R (-τ)) hc
    (actualQ_first_time R T hR p himage hT c p₀ hp he a ht)
    (first_transport_hasDerivAt R (actualQ R T hR p himage t) a t).hasDerivWithinAt
  simpa only [FreeTransport.transport_add] using h

theorem actualQ_second_material (a b : RealPosition) {t : ℝ} (ht : t∈Icc 0 T) :
    HasDerivWithinAt (fun τ => transport R (-τ)
      (spatialDerivative R 2 (by omega) ![a,b] (actualQ R T hR p himage τ)))
      (transport R (-t) (secondRate R T hR p himage a b t+
        fieldAdvection R (secondDerivativeField R (actualQ R T hR p himage t) a b))) (Icc 0 T) t := by
  have hc : Continuous (fun z : ℝ×Distribution R => transportCLM R (-z.1) z.2) :=
    (TransportDuhamel.transport_joint_continuous R).comp (continuous_fst.neg.prodMk continuous_snd)
  have h := strong_family_hasDerivWithinAt (fun τ => transportCLM R (-τ)) hc
    (actualQ_second_time R T hR p himage hT c p₀ hp he a b ht)
    (second_transport_hasDerivAt R (actualQ R T hR p himage t) a b t).hasDerivWithinAt
  simpa only [FreeTransport.transport_add] using h
end Actual

end
end Resonance.ActualCoframeLowTime

#check Resonance.ActualCoframeLowTime.actualQ_ordered_parameter
#check Resonance.ActualCoframeLowTime.actualQ_first_path
#check Resonance.ActualCoframeLowTime.actualQ_second_path
#check Resonance.ActualCoframeLowTime.actualQ_material
#check Resonance.ActualCoframeLowTime.actualQ_first_time
#check Resonance.ActualCoframeLowTime.actualQ_second_time
#check Resonance.ActualCoframeLowTime.actualQ_first_material
#check Resonance.ActualCoframeLowTime.actualQ_second_material
#print axioms Resonance.ActualCoframeLowTime.actualQ_ordered_parameter
#print axioms Resonance.ActualCoframeLowTime.actualQ_first_path
#print axioms Resonance.ActualCoframeLowTime.actualQ_second_path
#print axioms Resonance.ActualCoframeLowTime.actualQ_material
#print axioms Resonance.ActualCoframeLowTime.actualQ_first_time
#print axioms Resonance.ActualCoframeLowTime.actualQ_second_time
#print axioms Resonance.ActualCoframeLowTime.actualQ_first_material
#print axioms Resonance.ActualCoframeLowTime.actualQ_second_material
