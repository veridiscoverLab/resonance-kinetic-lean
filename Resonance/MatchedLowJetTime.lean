import Resonance.LowSpatialMaterialDerivative

/-! Time derivatives of the first and second actual matched-parameter jets.
They are read from the original kinetic moments, with no collision-rate term
and no assumed fourth spatial derivative. -/
open Set Function
open scoped ContDiff
namespace Resonance.MatchedLowJetTime
noncomputable section
open FreeTransport JetCollision SpatialChainRule JetEnergy ActualMatchedMoments
open Thermodynamics ThermodynamicChart LowSpatialMaterialDerivative ContinuousCollisionMoments
set_option maxHeartbeats 1500000

abbrev Data := Parameter×(Parameter×(Parameter×Parameter))

def firstComposition (F : Parameter→Parameter) (d : Data) : Parameter :=
  fderiv ℝ F d.1 d.2.1

def secondComposition (F : Parameter→Parameter) (d : Data) : Parameter :=
  fderiv ℝ (fderiv ℝ F) d.1 d.2.1 d.2.2.1+fderiv ℝ F d.1 d.2.2.2

theorem firstComposition_contDiffAt {F : Parameter→Parameter} {d : Data}
    (hF : ContDiffAt ℝ 3 F d.1) : ContDiffAt ℝ 1 (firstComposition F) d := by
  have h : ContDiffAt ℝ 1 (fun u : Data => fderiv ℝ F u.1) d :=
    (hF.fderiv_right (by norm_num : (1:WithTop ℕ∞)+1≤3)).comp d contDiffAt_fst
  exact h.clm_apply contDiffAt_snd.fst

theorem secondComposition_contDiffAt {F : Parameter→Parameter} {d : Data}
    (hF : ContDiffAt ℝ 3 F d.1) : ContDiffAt ℝ 1 (secondComposition F) d := by
  have h1 : ContDiffAt ℝ 2 (fderiv ℝ F) d.1 := hF.fderiv_right (by norm_num)
  have h2 : ContDiffAt ℝ 1 (fun u : Data => fderiv ℝ (fderiv ℝ F) u.1) d :=
    (h1.fderiv_right (by norm_num)).comp d contDiffAt_fst
  have h3 : ContDiffAt ℝ 1 (fun u : Data => fderiv ℝ F u.1) d :=
    (hF.fderiv_right (by norm_num : (1:WithTop ℕ∞)+1≤3)).comp d contDiffAt_fst
  exact ((h2.clm_apply contDiffAt_snd.fst).clm_apply contDiffAt_snd.snd.fst).add
    (h3.clm_apply contDiffAt_snd.snd.snd)

def momentJet (R : ℝ) (p : Space R) (n : ℕ) (hn : n≤3)
    (v : Fin n→RealPosition) (x : RealPosition) : Parameter :=
  actualMoments R (spatialDerivative R n hn v p) (torusQuotient x)

theorem momentJet_actual (R : ℝ) (p : Space R) (n : ℕ) (hn : n≤3)
    (v : Fin n→RealPosition) (x : RealPosition) :
    momentJet R p n hn v x=iteratedFDeriv ℝ n
      (fun y => actualMoments R (readback p) (torusQuotient y)) x v := by
  have h := (moments R).iteratedFDeriv_comp_left (x := x)
    (SpatialJetSpace.toDistribution_contDiff p).contDiffAt (by exact_mod_cast hn)
  have he : (spatialDerivative R n hn v p).curry (torusQuotient x)=
      iteratedFDeriv ℝ n (realLift (readback p)) x v := by
    ext k
    exact derivative_at_quotient R p n hn v x k
  change moments R ((spatialDerivative R n hn v p).curry (torusQuotient x))=_
  rw [he]
  exact (congrArg (fun A => A v) h).symm

def momentData (R : ℝ) (p : Space R) (x a b : RealPosition) : Data :=
  (actualMoments R (readback p) (torusQuotient x),momentJet R p 1 (by omega) ![a] x,
    momentJet R p 1 (by omega) ![b] x,momentJet R p 2 (by omega) ![a,b] x)

def momentDataRate (R : ℝ) (p : Space R) (x a b : RealPosition) : Data :=
  (-divergenceVector R p x,
    -actualMoments R (fieldAdvection R (firstDerivativeField R p a)) (torusQuotient x),
    -actualMoments R (fieldAdvection R (firstDerivativeField R p b)) (torusQuotient x),
    -actualMoments R (fieldAdvection R (secondDerivativeField R p a b)) (torusQuotient x))

theorem matched_first_composition (R : ℝ) (hR : 0<R) (p : Space R) (x a b : RealPosition)
    (hx : actualMoments R (readback p) (torusQuotient x)∈momentImage R) :
    iteratedFDeriv ℝ 1 (fun y => matchedValue R hR (readback p) (torusQuotient y)) x ![a]=
      firstComposition (momentInverse R hR) (momentData R p x a b) := by
  have h := (momentInverse_hasFDerivAt R hR _ hx).differentiableAt.hasFDerivAt.comp x
    ((actualMoments_real_contDiff R p).differentiable (by norm_num) x).hasFDerivAt
  rw [iteratedFDeriv_one_apply]
  change (fderiv ℝ (momentInverse R hR ∘
    (fun y => actualMoments R (readback p) (torusQuotient y))) x) a=_
  rw [h.fderiv]
  simp only [firstComposition,momentData,momentJet_actual,iteratedFDeriv_one_apply,
    ContinuousLinearMap.comp_apply,Matrix.cons_val_zero]

theorem matched_second_composition (R : ℝ) (hR : 0<R) (p : Space R) (x a b : RealPosition)
    (hx : actualMoments R (readback p) (torusQuotient x)∈momentImage R) :
    iteratedFDeriv ℝ 2 (fun y => matchedValue R hR (readback p) (torusQuotient y)) x ![a,b]=
      secondComposition (momentInverse R hR) (momentData R p x a b) := by
  have h := SpatialChainRule.composition_second
    (f := fun y : RealPosition => actualMoments R (readback p) (torusQuotient y)) (x := x)
    (ThermodynamicJets.momentInverse_contDiffAt_finite R hR 2 _ hx)
    ((actualMoments_real_contDiff R p).of_le (by norm_num)).contDiffAt a b
  change iteratedFDeriv ℝ 2 (fun y => matchedValue R hR (readback p) (torusQuotient y)) x ![a,b]=_ at h
  rw [h]
  simp only [secondComposition,momentData,momentJet_actual,iteratedFDeriv_two_apply,
    iteratedFDeriv_one_apply,Matrix.cons_val_zero,Matrix.cons_val_one]

theorem actual_momentData_derivative {R T : ℝ} (hR : 0≤R) (hT : 0≤T)
    (c : ℝ) (p₀ : Space R) (p : ℝ→Space R) (hp : ContinuousOn p (Icc 0 T))
    (he : ∀ t∈Icc 0 T,readback (p t)=transport R t (readback p₀)+
      ∫ s in (0:ℝ)..t,c • transport R (t-s)
        (SpatialCollision.collision R hR (readback (p s))))
    (x a b : RealPosition) {t : ℝ} (ht : t∈Icc 0 T) :
    HasDerivWithinAt (fun τ => momentData R (p τ) x a b)
      (momentDataRate R (p t) x a b) (Icc 0 T) t := by
  have h1 (v : RealPosition) : HasDerivWithinAt (fun τ => momentJet R (p τ) 1 (by omega) ![v] x)
      (-actualMoments R (fieldAdvection R (firstDerivativeField R (p t) v)) (torusQuotient x))
      (Icc 0 T) t := by
    apply hasDerivWithinAt_pi.mpr
    intro i
    exact (ContinuousMap.evalCLM (R := ℝ) (torusQuotient x)).hasFDerivAt.comp_hasDerivWithinAt t
      (original_mild_first_moment_derivative hR hT c p₀ p hp he (basisParameter i) v ht)
  have h2 : HasDerivWithinAt (fun τ => momentJet R (p τ) 2 (by omega) ![a,b] x)
      (-actualMoments R (fieldAdvection R (secondDerivativeField R (p t) a b)) (torusQuotient x))
      (Icc 0 T) t := by
    apply hasDerivWithinAt_pi.mpr
    intro i
    exact (ContinuousMap.evalCLM (R := ℝ) (torusQuotient x)).hasFDerivAt.comp_hasDerivWithinAt t
      (original_mild_second_moment_derivative hR hT c p₀ p hp he (basisParameter i) a b ht)
  exact (actual_moment_derivative hR hT c p₀ p hp he x ht).prodMk ((h1 a).prodMk ((h1 b).prodMk h2))

theorem actual_matched_first_jet_time {R T : ℝ} (hR : 0<R) (hT : 0≤T)
    (c : ℝ) (p₀ : Space R) (p : ℝ→Space R) (hp : ContinuousOn p (Icc 0 T))
    (he : ∀ t∈Icc 0 T,readback (p t)=transport R t (readback p₀)+
      ∫ s in (0:ℝ)..t,c • transport R (t-s)
        (SpatialCollision.collision R hR.le (readback (p s))))
    (himage : ∀ τ∈Icc 0 T,∀ X,actualMoments R (readback (p τ)) X∈momentImage R)
    (x a b : RealPosition) {t : ℝ} (ht : t∈Icc 0 T) :
    HasDerivWithinAt (fun τ => iteratedFDeriv ℝ 1
      (fun y => matchedValue R hR (readback (p τ)) (torusQuotient y)) x ![a])
      (fderiv ℝ (firstComposition (momentInverse R hR)) (momentData R (p t) x a b)
        (momentDataRate R (p t) x a b)) (Icc 0 T) t := by
  have h := ((firstComposition_contDiffAt (d := momentData R (p t) x a b)
    (ThermodynamicJets.momentInverse_contDiffAt_finite R hR 3 _
      (himage t ht (torusQuotient x)))).differentiableAt (by norm_num)).hasFDerivAt.comp_hasDerivWithinAt t
    (actual_momentData_derivative hR.le hT c p₀ p hp he x a b ht)
  exact h.congr_of_mem (fun τ hτ => matched_first_composition R hR (p τ) x a b
    (himage τ hτ (torusQuotient x))) ht

theorem actual_matched_second_jet_time {R T : ℝ} (hR : 0<R) (hT : 0≤T)
    (c : ℝ) (p₀ : Space R) (p : ℝ→Space R) (hp : ContinuousOn p (Icc 0 T))
    (he : ∀ t∈Icc 0 T,readback (p t)=transport R t (readback p₀)+
      ∫ s in (0:ℝ)..t,c • transport R (t-s)
        (SpatialCollision.collision R hR.le (readback (p s))))
    (himage : ∀ τ∈Icc 0 T,∀ X,actualMoments R (readback (p τ)) X∈momentImage R)
    (x a b : RealPosition) {t : ℝ} (ht : t∈Icc 0 T) :
    HasDerivWithinAt (fun τ => iteratedFDeriv ℝ 2
      (fun y => matchedValue R hR (readback (p τ)) (torusQuotient y)) x ![a,b])
      (fderiv ℝ (secondComposition (momentInverse R hR)) (momentData R (p t) x a b)
        (momentDataRate R (p t) x a b)) (Icc 0 T) t := by
  have h := ((secondComposition_contDiffAt (d := momentData R (p t) x a b)
    (ThermodynamicJets.momentInverse_contDiffAt_finite R hR 3 _
      (himage t ht (torusQuotient x)))).differentiableAt (by norm_num)).hasFDerivAt.comp_hasDerivWithinAt t
    (actual_momentData_derivative hR.le hT c p₀ p hp he x a b ht)
  exact h.congr_of_mem (fun τ hτ => matched_second_composition R hR (p τ) x a b
    (himage τ hτ (torusQuotient x))) ht

end
end Resonance.MatchedLowJetTime

#check Resonance.MatchedLowJetTime.firstComposition_contDiffAt
#check Resonance.MatchedLowJetTime.secondComposition_contDiffAt
#check Resonance.MatchedLowJetTime.momentJet_actual
#check Resonance.MatchedLowJetTime.matched_first_composition
#check Resonance.MatchedLowJetTime.matched_second_composition
#check Resonance.MatchedLowJetTime.actual_momentData_derivative
#check Resonance.MatchedLowJetTime.actual_matched_first_jet_time
#check Resonance.MatchedLowJetTime.actual_matched_second_jet_time
#print axioms Resonance.MatchedLowJetTime.firstComposition_contDiffAt
#print axioms Resonance.MatchedLowJetTime.secondComposition_contDiffAt
#print axioms Resonance.MatchedLowJetTime.momentJet_actual
#print axioms Resonance.MatchedLowJetTime.matched_first_composition
#print axioms Resonance.MatchedLowJetTime.matched_second_composition
#print axioms Resonance.MatchedLowJetTime.actual_momentData_derivative
#print axioms Resonance.MatchedLowJetTime.actual_matched_first_jet_time
#print axioms Resonance.MatchedLowJetTime.actual_matched_second_jet_time
