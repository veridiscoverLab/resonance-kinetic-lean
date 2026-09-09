import Resonance.MatchedLowJetTime

/-! Uniform-in-space time differentiation of the actual matched low jets.
The strong derivative follows from the true finite-dimensional chain rule,
compact spatial evaluation, and the original kinetic moment equations. -/
open Set Function
open scoped ContDiff
namespace Resonance.MatchedJetStrongTime
noncomputable section
open FreeTransport JetCollision SpatialChainRule JetEnergy ActualMatchedMoments
open Thermodynamics ThermodynamicChart MatchedLowJetTime LowSpatialMaterialDerivative
open MatchedContinuousTime TransportMaterialDerivative
set_option maxHeartbeats 1500000

abbrev dataDomain (R : ℝ) : Set Data := Prod.fst ⁻¹' momentImage R

def dataField (R : ℝ) (p : Space R) (a b : RealPosition) : C(SpatialTorus,Data) :=
  (actualMoments R (readback p)).prodMk
    ((actualMoments R (spatialDerivative R 1 (by omega) ![a] p)).prodMk
      ((actualMoments R (spatialDerivative R 1 (by omega) ![b] p)).prodMk
        (actualMoments R (spatialDerivative R 2 (by omega) ![a,b] p))))

def dataRateField (R : ℝ) (p : Space R) (a b : RealPosition) : C(SpatialTorus,Data) :=
  (-actualMoments R (advection R p)).prodMk
    ((-actualMoments R (fieldAdvection R (firstDerivativeField R p a))).prodMk
      ((-actualMoments R (fieldAdvection R (firstDerivativeField R p b))).prodMk
        (-actualMoments R (fieldAdvection R (secondDerivativeField R p a b)))))

theorem dataField_apply (R : ℝ) (p : Space R) (a b x : RealPosition) :
    dataField R p a b (torusQuotient x)=momentData R p x a b := rfl

theorem dataRateField_apply (R : ℝ) (p : Space R) (a b x : RealPosition) :
    dataRateField R p a b (torusQuotient x)=momentDataRate R p x a b := by
  apply Prod.ext
  · ext i
    change -ContinuousCollisionMoments.spatialMoment R (basisParameter i)
      (advection R p) (torusQuotient x) = -JetMomentDynamics.fluxDivergence R (basisParameter i) p x
    rw [JetMomentDynamics.moment_advection_eq_fluxDivergence]
  · rfl

theorem firstAdvection_continuous (R : ℝ) (a : RealPosition) :
    Continuous (fun p : Space R => fieldAdvection R (firstDerivativeField R p a)) := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  have hA : Continuous (fun z : Space R×Phase R => z.1.val.2.2.1 z.2.1) :=
    (((continuous_subtype_val.comp continuous_fst).snd.snd.fst).eval continuous_snd.fst)
  have hv : Continuous (fun z : Space R×Phase R => velocity R z.2.2) := by
    unfold velocity
    apply continuous_pi
    intro j
    fun_prop
  exact ((hA.clm_apply hv).clm_apply continuous_const).eval continuous_snd.snd

theorem secondAdvection_continuous (R : ℝ) (a b : RealPosition) :
    Continuous (fun p : Space R => fieldAdvection R (secondDerivativeField R p a b)) := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  have hA : Continuous (fun z : Space R×Phase R => z.1.val.2.2.2 z.2.1) :=
    (((continuous_subtype_val.comp continuous_fst).snd.snd.snd).eval continuous_snd.fst)
  have hv : Continuous (fun z : Space R×Phase R => velocity R z.2.2) := by
    unfold velocity
    apply continuous_pi
    intro j
    fun_prop
  exact (((hA.clm_apply hv).clm_apply continuous_const).clm_apply continuous_const).eval continuous_snd.snd

theorem dataField_continuous (R : ℝ) (a b : RealPosition) : Continuous (fun p : Space R => dataField R p a b) := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  have h0 : Continuous (fun z : Space R×SpatialTorus => actualMoments R (readback z.1) z.2) :=
    (((actualMoments_continuous R).comp (JetLocalKinetics.readbackOperator R).continuous).comp
      continuous_fst).eval continuous_snd
  have h (n : ℕ) (hn : n≤3) (v : Fin n→RealPosition) :
      Continuous (fun z : Space R×SpatialTorus => actualMoments R (spatialDerivative R n hn v z.1) z.2) :=
    (((actualMoments_continuous R).comp (spatialDerivative R n hn v).continuous).comp
      continuous_fst).eval continuous_snd
  exact h0.prodMk ((h 1 (by omega) ![a]).prodMk
    ((h 1 (by omega) ![b]).prodMk (h 2 (by omega) ![a,b])))

theorem dataRateField_continuous (R : ℝ) (a b : RealPosition) : Continuous (fun p : Space R => dataRateField R p a b) := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  have h (u : Space R→Distribution R) (hu : Continuous u) :
      Continuous (fun z : Space R×SpatialTorus => -actualMoments R (u z.1) z.2) :=
    ((((actualMoments_continuous R).comp hu).comp continuous_fst).eval continuous_snd).neg
  exact (h _ (advection_continuous R)).prodMk
    ((h _ (firstAdvection_continuous R a)).prodMk
      ((h _ (firstAdvection_continuous R b)).prodMk (h _ (secondAdvection_continuous R a b))))

section Composition
variable (R : ℝ) (hR : 0<R) (F : Data→Parameter)
  (hF : ContDiffOn ℝ 1 F (dataDomain R))

def compositionField (u : C(SpatialTorus,Data)) (hu : ∀ X,u X∈dataDomain R) : C(SpatialTorus,Parameter) :=
  ⟨fun X => F (u X),hF.continuousOn.comp_continuous u.continuous hu⟩

def compositionRateField (u d : C(SpatialTorus,Data)) (hu : ∀ X,u X∈dataDomain R) : C(SpatialTorus,Parameter) :=
  ⟨fun X => fderiv ℝ F (u X) (d X),by
    have hd := hF.continuousOn_fderiv_of_isOpen ((momentImage_isOpen R hR).preimage continuous_fst) le_rfl
    exact (hd.comp_continuous u.continuous hu).clm_apply d.continuous⟩

variable (s : Set ℝ) (u d : ℝ→C(SpatialTorus,Data))
  (hu : ∀ t∈s,∀ X,u t X∈dataDomain R)

def compositionPath (t : ℝ) : C(SpatialTorus,Parameter) := by
  classical
  exact if ht : t∈s then compositionField R F hF (u t) (hu t ht) else 0

def compositionRatePath (t : ℝ) : C(SpatialTorus,Parameter) := by
  classical
  exact if ht : t∈s then compositionRateField R hR F hF (u t) (d t) (hu t ht) else 0

theorem compositionPath_apply {t : ℝ} (ht : t∈s) (X : SpatialTorus) :
    compositionPath R F hF s u hu t X=F (u t X) := by simp only [compositionPath,dif_pos ht]; rfl

theorem compositionRatePath_apply {t : ℝ} (ht : t∈s) (X : SpatialTorus) :
    compositionRatePath R hR F hF s u d hu t X=fderiv ℝ F (u t X) (d t X) := by
  simp only [compositionRatePath,dif_pos ht]; rfl

theorem compositionRatePath_continuousOn (huc : ContinuousOn u s) (hdc : ContinuousOn d s) :
    ContinuousOn (compositionRatePath R hR F hF s u d hu) s := by
  apply ContinuousMap.continuousOn_of_continuousOn_uncurry
  have hi := hF.continuousOn_fderiv_of_isOpen ((momentImage_isOpen R hR).preimage continuous_fst) le_rfl
  have hc : ContinuousOn (fun z : ℝ×SpatialTorus => u z.1 z.2) (s×ˢuniv) :=
    (huc.comp continuous_fst.continuousOn (fun _ hz => hz.1)).eval continuous_snd.continuousOn
  have hd : ContinuousOn (fun z : ℝ×SpatialTorus => d z.1 z.2) (s×ˢuniv) :=
    (hdc.comp continuous_fst.continuousOn (fun _ hz => hz.1)).eval continuous_snd.continuousOn
  have h := (hi.comp hc (fun z hz => hu z.1 hz.1 z.2)).clm_apply hd
  exact h.congr (fun z hz => compositionRatePath_apply R hR F hF s u d hu hz.1 z.2)

theorem compositionPath_hasDerivWithinAt (hs : Convex ℝ s)
    (huc : ContinuousOn u s) (hdc : ContinuousOn d s)
    (hder : ∀ t∈s,∀ X,HasDerivWithinAt (fun τ => u τ X) (d t X) s t)
    {t : ℝ} (ht : t∈s) :
    HasDerivWithinAt (compositionPath R F hF s u hu)
      (compositionRatePath R hR F hF s u d hu t) s t := by
  apply WithinEvaluationDerivative.hasDerivWithinAt_of_evaluations hs ht
    (compositionRatePath_continuousOn R hR F hF s u d hu huc hdc t ht)
  intro τ hτ X
  have hf : HasFDerivAt F (fderiv ℝ F (u τ X)) (u τ X) :=
    ((hF (u τ X) (hu τ hτ X)).contDiffAt
      (((momentImage_isOpen R hR).preimage continuous_fst).mem_nhds (hu τ hτ X))).differentiableAt
        (by norm_num) |>.hasFDerivAt
  rw [compositionRatePath_apply R hR F hF s u d hu hτ X]
  exact (hf.comp_hasDerivWithinAt τ (hder τ hτ X)).congr_of_mem
    (fun t' ht' => compositionPath_apply R F hF s u hu ht' X) hτ
end Composition

theorem firstComposition_contDiffOn (R : ℝ) (hR : 0<R) :
    ContDiffOn ℝ 1 (firstComposition (momentInverse R hR)) (dataDomain R) :=
  fun _d hd => (firstComposition_contDiffAt
    (ThermodynamicJets.momentInverse_contDiffAt_finite R hR 3 _ hd)).contDiffWithinAt

theorem secondComposition_contDiffOn (R : ℝ) (hR : 0<R) :
    ContDiffOn ℝ 1 (secondComposition (momentInverse R hR)) (dataDomain R) :=
  fun _d hd => (secondComposition_contDiffAt
    (ThermodynamicJets.momentInverse_contDiffAt_finite R hR 3 _ hd)).contDiffWithinAt

theorem actual_dataField_derivative {R T : ℝ} (hR : 0≤R) (hT : 0≤T)
    (c : ℝ) (p₀ : Space R) (p : ℝ→Space R) (hp : ContinuousOn p (Icc 0 T))
    (he : ∀ t∈Icc 0 T,readback (p t)=transport R t (readback p₀)+
      ∫ s in (0:ℝ)..t,c • transport R (t-s)
        (SpatialCollision.collision R hR (readback (p s))))
    (a b : RealPosition) {t : ℝ} (ht : t∈Icc 0 T) (X : SpatialTorus) :
    HasDerivWithinAt (fun τ => dataField R (p τ) a b X)
      (dataRateField R (p t) a b X) (Icc 0 T) t := by
  obtain ⟨x,rfl⟩ := SpatialJetSpace.torusQuotient_surjective X
  simp only [dataField_apply,dataRateField_apply]
  exact actual_momentData_derivative hR hT c p₀ p hp he x a b ht

theorem actual_jet_composition_strong_time {R T : ℝ} (hR : 0<R) (hT : 0≤T)
    (c : ℝ) (p₀ : Space R) (p : ℝ→Space R) (hp : ContinuousOn p (Icc 0 T))
    (he : ∀ t∈Icc 0 T,readback (p t)=transport R t (readback p₀)+
      ∫ s in (0:ℝ)..t,c • transport R (t-s)
        (SpatialCollision.collision R hR.le (readback (p s))))
    (himage : ∀ τ∈Icc 0 T,∀ X,actualMoments R (readback (p τ)) X∈momentImage R)
    (F : Data→Parameter) (hF : ContDiffOn ℝ 1 F (dataDomain R))
    (a b : RealPosition) {t : ℝ} (ht : t∈Icc 0 T) :
    HasDerivWithinAt
      (compositionPath R F hF (Icc 0 T) (fun τ => dataField R (p τ) a b) himage)
      (compositionRatePath R hR F hF (Icc 0 T) (fun τ => dataField R (p τ) a b)
        (fun τ => dataRateField R (p τ) a b) himage t) (Icc 0 T) t := by
  apply compositionPath_hasDerivWithinAt R hR F hF (Icc 0 T) _ _ himage (convex_Icc 0 T)
    ((dataField_continuous R a b).comp_continuousOn hp)
    ((dataRateField_continuous R a b).comp_continuousOn hp)
    (fun τ hτ X => actual_dataField_derivative hR.le hT c p₀ p hp he a b hτ X) ht

theorem actual_first_jet_path_value {R T : ℝ} (hR : 0<R) (p : ℝ→Space R)
    (himage : ∀ τ∈Icc 0 T,∀ X,actualMoments R (readback (p τ)) X∈momentImage R)
    (a b x : RealPosition) {t : ℝ} (ht : t∈Icc 0 T) :
    compositionPath R (firstComposition (momentInverse R hR)) (firstComposition_contDiffOn R hR)
      (Icc 0 T) (fun τ => dataField R (p τ) a b) himage t (torusQuotient x)=
    iteratedFDeriv ℝ 1 (fun y => matchedValue R hR (readback (p t)) (torusQuotient y)) x ![a] := by
  rw [compositionPath_apply R _ _ _ _ himage ht,dataField_apply]
  exact (matched_first_composition R hR (p t) x a b (himage t ht (torusQuotient x))).symm

theorem actual_second_jet_path_value {R T : ℝ} (hR : 0<R) (p : ℝ→Space R)
    (himage : ∀ τ∈Icc 0 T,∀ X,actualMoments R (readback (p τ)) X∈momentImage R)
    (a b x : RealPosition) {t : ℝ} (ht : t∈Icc 0 T) :
    compositionPath R (secondComposition (momentInverse R hR)) (secondComposition_contDiffOn R hR)
      (Icc 0 T) (fun τ => dataField R (p τ) a b) himage t (torusQuotient x)=
    iteratedFDeriv ℝ 2 (fun y => matchedValue R hR (readback (p t)) (torusQuotient y)) x ![a,b] := by
  rw [compositionPath_apply R _ _ _ _ himage ht,dataField_apply]
  exact (matched_second_composition R hR (p t) x a b (himage t ht (torusQuotient x))).symm

theorem actual_first_jet_strong_derivative {R T : ℝ} (hR : 0<R) (hT : 0≤T)
    (c : ℝ) (p₀ : Space R) (p : ℝ→Space R) (hp : ContinuousOn p (Icc 0 T))
    (he : ∀ t∈Icc 0 T,readback (p t)=transport R t (readback p₀)+
      ∫ s in (0:ℝ)..t,c • transport R (t-s)
        (SpatialCollision.collision R hR.le (readback (p s))))
    (himage : ∀ τ∈Icc 0 T,∀ X,actualMoments R (readback (p τ)) X∈momentImage R)
    (a b : RealPosition) {t : ℝ} (ht : t∈Icc 0 T) :
    HasDerivWithinAt
      (compositionPath R (firstComposition (momentInverse R hR)) (firstComposition_contDiffOn R hR)
        (Icc 0 T) (fun τ => dataField R (p τ) a b) himage)
      (compositionRatePath R hR (firstComposition (momentInverse R hR)) (firstComposition_contDiffOn R hR)
        (Icc 0 T) (fun τ => dataField R (p τ) a b)
        (fun τ => dataRateField R (p τ) a b) himage t) (Icc 0 T) t :=
  actual_jet_composition_strong_time hR hT c p₀ p hp he himage _ (firstComposition_contDiffOn R hR) a b ht

theorem actual_second_jet_strong_derivative {R T : ℝ} (hR : 0<R) (hT : 0≤T)
    (c : ℝ) (p₀ : Space R) (p : ℝ→Space R) (hp : ContinuousOn p (Icc 0 T))
    (he : ∀ t∈Icc 0 T,readback (p t)=transport R t (readback p₀)+
      ∫ s in (0:ℝ)..t,c • transport R (t-s)
        (SpatialCollision.collision R hR.le (readback (p s))))
    (himage : ∀ τ∈Icc 0 T,∀ X,actualMoments R (readback (p τ)) X∈momentImage R)
    (a b : RealPosition) {t : ℝ} (ht : t∈Icc 0 T) :
    HasDerivWithinAt
      (compositionPath R (secondComposition (momentInverse R hR)) (secondComposition_contDiffOn R hR)
        (Icc 0 T) (fun τ => dataField R (p τ) a b) himage)
      (compositionRatePath R hR (secondComposition (momentInverse R hR)) (secondComposition_contDiffOn R hR)
        (Icc 0 T) (fun τ => dataField R (p τ) a b)
        (fun τ => dataRateField R (p τ) a b) himage t) (Icc 0 T) t :=
  actual_jet_composition_strong_time hR hT c p₀ p hp he himage _ (secondComposition_contDiffOn R hR) a b ht

end
end Resonance.MatchedJetStrongTime

#check Resonance.MatchedJetStrongTime.dataField_apply
#check Resonance.MatchedJetStrongTime.dataRateField_apply
#check Resonance.MatchedJetStrongTime.firstAdvection_continuous
#check Resonance.MatchedJetStrongTime.secondAdvection_continuous
#check Resonance.MatchedJetStrongTime.dataField_continuous
#check Resonance.MatchedJetStrongTime.dataRateField_continuous
#check Resonance.MatchedJetStrongTime.compositionPath_apply
#check Resonance.MatchedJetStrongTime.compositionRatePath_apply
#check Resonance.MatchedJetStrongTime.compositionRatePath_continuousOn
#check Resonance.MatchedJetStrongTime.compositionPath_hasDerivWithinAt
#check Resonance.MatchedJetStrongTime.firstComposition_contDiffOn
#check Resonance.MatchedJetStrongTime.secondComposition_contDiffOn
#check Resonance.MatchedJetStrongTime.actual_dataField_derivative
#check Resonance.MatchedJetStrongTime.actual_jet_composition_strong_time
#check Resonance.MatchedJetStrongTime.actual_first_jet_path_value
#check Resonance.MatchedJetStrongTime.actual_second_jet_path_value
#check Resonance.MatchedJetStrongTime.actual_first_jet_strong_derivative
#check Resonance.MatchedJetStrongTime.actual_second_jet_strong_derivative
#print axioms Resonance.MatchedJetStrongTime.dataField_apply
#print axioms Resonance.MatchedJetStrongTime.dataRateField_apply
#print axioms Resonance.MatchedJetStrongTime.firstAdvection_continuous
#print axioms Resonance.MatchedJetStrongTime.secondAdvection_continuous
#print axioms Resonance.MatchedJetStrongTime.dataField_continuous
#print axioms Resonance.MatchedJetStrongTime.dataRateField_continuous
#print axioms Resonance.MatchedJetStrongTime.compositionPath_apply
#print axioms Resonance.MatchedJetStrongTime.compositionRatePath_apply
#print axioms Resonance.MatchedJetStrongTime.compositionRatePath_continuousOn
#print axioms Resonance.MatchedJetStrongTime.compositionPath_hasDerivWithinAt
#print axioms Resonance.MatchedJetStrongTime.firstComposition_contDiffOn
#print axioms Resonance.MatchedJetStrongTime.secondComposition_contDiffOn
#print axioms Resonance.MatchedJetStrongTime.actual_dataField_derivative
#print axioms Resonance.MatchedJetStrongTime.actual_jet_composition_strong_time
#print axioms Resonance.MatchedJetStrongTime.actual_first_jet_path_value
#print axioms Resonance.MatchedJetStrongTime.actual_second_jet_path_value
#print axioms Resonance.MatchedJetStrongTime.actual_first_jet_strong_derivative
#print axioms Resonance.MatchedJetStrongTime.actual_second_jet_strong_derivative
