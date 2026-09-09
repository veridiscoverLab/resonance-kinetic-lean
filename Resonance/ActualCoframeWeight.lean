import Resonance.MatchedContinuousTime

/-! The actual reciprocal matched profile as a compatible C³ weight, with
its time derivative proved only in C(phase). This instantiates the physical
weighted H³ energy identity on the same original mild solution. -/
open Set MeasureTheory
open scoped BigOperators
namespace Resonance.ActualCoframeWeight
noncomputable section
open FreeTransport JetCollision SpatialChainRule SpatialJetSpace SpatialJetDescent
open ContinuousCollisionMoments JetMomentDynamics ActualMatchedMoments MatchedContinuousTime
open Thermodynamics ThermodynamicChart TransportMaterialDerivative WeightedPhysicalForm WeightedJointMeasure
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 30000

def denominatorCubeLinear (R : ℝ) : Parameter →ₗ[ℝ] CubeFunction R where
  toFun := momentTest R
  map_add' a b := by
    ext k
    change Entropy.denominator Entropy.fiveInvariants (a+b) (coordinates k)=
      Entropy.denominator Entropy.fiveInvariants a (coordinates k)+
      Entropy.denominator Entropy.fiveInvariants b (coordinates k)
    simp_rw [←denominatorCLM_apply]
    exact map_add _ a b
  map_smul' c a := by
    ext k
    change Entropy.denominator Entropy.fiveInvariants (c • a) (coordinates k)=
      c • Entropy.denominator Entropy.fiveInvariants a (coordinates k)
    simp_rw [←denominatorCLM_apply]
    exact map_smul _ c a

def denominatorCube (R : ℝ) : Parameter →L[ℝ] CubeFunction R :=
  ⟨denominatorCubeLinear R,by
    apply ContinuousMap.continuous_of_continuous_uncurry
    change Continuous (fun z : Parameter×MomentumDomain R => reciprocalProfile z.1 z.2)
    have h : Continuous (fun z : Parameter×MomentumDomain R =>
        denominatorCLM (coordinates z.2) z.1) := (((denominatorCLM_continuous.comp coordinates_continuous).comp
      continuous_subtype_val).comp continuous_snd).clm_apply continuous_fst
    simpa only [denominatorCLM_apply] using h⟩

def denominatorFieldLinear (R : ℝ) : C(SpatialTorus,Parameter) →ₗ[ℝ] Distribution R where
  toFun := parameterWeight R
  map_add' a b := by
    ext z
    change Entropy.denominator Entropy.fiveInvariants (a z.1+b z.1) (coordinates z.2)=
      Entropy.denominator Entropy.fiveInvariants (a z.1) (coordinates z.2)+
      Entropy.denominator Entropy.fiveInvariants (b z.1) (coordinates z.2)
    simp_rw [←denominatorCLM_apply]
    exact map_add _ _ _
  map_smul' c a := by
    ext z
    change Entropy.denominator Entropy.fiveInvariants (c • a z.1) (coordinates z.2)=
      c • Entropy.denominator Entropy.fiveInvariants (a z.1) (coordinates z.2)
    simp_rw [←denominatorCLM_apply]
    exact map_smul _ _ _

def denominatorField (R : ℝ) : C(SpatialTorus,Parameter) →L[ℝ] Distribution R :=
  ⟨denominatorFieldLinear R,by
    apply ContinuousMap.continuous_of_continuous_uncurry
    change Continuous (fun z : C(SpatialTorus,Parameter)×Phase R => reciprocalProfile (z.1 z.2.1) z.2.2)
    have h : Continuous (fun z : C(SpatialTorus,Parameter)×Phase R =>
        denominatorCLM (coordinates z.2.2) (z.1 z.2.1)) := (((denominatorCLM_continuous.comp coordinates_continuous).comp
      continuous_subtype_val).comp continuous_snd.snd).clm_apply
      (continuous_fst.eval continuous_snd.fst)
    simpa only [denominatorCLM_apply] using h⟩

theorem denominatorField_realLift (R : ℝ) (a : C(SpatialTorus,Parameter)) :
    realLift (denominatorField R a)=fun x => denominatorCube R (a (torusQuotient x)) := rfl

theorem actual_parameterPath_contDiff (R : ℝ) (hR : 0<R) (s : Set ℝ) (p : ℝ→Space R)
    (himage : ∀ t∈s,∀ X,actualMoments R (readback (p t)) X∈momentImage R) (t : ℝ) :
    ContDiff ℝ 3 (fun x => parameterPath R hR s (fun τ => readback (p τ)) himage t (torusQuotient x)) := by
  by_cases ht : t∈s
  · have he : (fun x => parameterPath R hR s (fun τ => readback (p τ)) himage t (torusQuotient x))=
        fun x => matchedValue R hR (readback (p t)) (torusQuotient x) :=
      funext (fun x => parameterPath_apply R hR s _ himage ht (torusQuotient x))
    rw [he]
    exact contDiff_iff_contDiffAt.mpr (fun x => matched_real_contDiffAt R hR (p t) x
      (himage t ht (torusQuotient x)))
  · simp only [parameterPath,dif_neg ht,ContinuousMap.zero_apply]
    exact contDiff_const

def coframeJet (R : ℝ) (hR : 0<R) (s : Set ℝ) (p : ℝ→Space R)
    (himage : ∀ t∈s,∀ X,actualMoments R (readback (p t)) X∈momentImage R) (t : ℝ) : Space R :=
  jetOfDistribution (denominatorField R (parameterPath R hR s (fun τ => readback (p τ)) himage t)) (by
    rw [denominatorField_realLift]
    exact (denominatorCube R).contDiff.comp (actual_parameterPath_contDiff R hR s p himage t))

theorem coframeJet_readback (R : ℝ) (hR : 0<R) (s : Set ℝ) (p : ℝ→Space R)
    (himage : ∀ t∈s,∀ X,actualMoments R (readback (p t)) X∈momentImage R) (t : ℝ) :
    readback (coframeJet R hR s p himage t)=
      denominatorField R (parameterPath R hR s (fun τ => readback (p τ)) himage t) :=
  jetOfDistribution_readback _ _

theorem coframeJet_actual_value (R : ℝ) (hR : 0<R) (s : Set ℝ) (p : ℝ→Space R)
    (himage : ∀ t∈s,∀ X,actualMoments R (readback (p t)) X∈momentImage R)
    {t : ℝ} (ht : t∈s) (z : Phase R) :
    readback (coframeJet R hR s p himage t) z=
      (profile (matchedValue R hR (readback (p t)) z.1) z.2)⁻¹ := by
  rw [coframeJet_readback]
  change reciprocalProfile (parameterPath R hR s _ himage t z.1) z.2=_
  rw [parameterPath_apply R hR s _ himage ht z.1,reciprocalProfile_eq_inv]

theorem coframeJet_positive (R : ℝ) (hR : 0<R) (s : Set ℝ) (p : ℝ→Space R)
    (himage : ∀ t∈s,∀ X,actualMoments R (readback (p t)) X∈momentImage R)
    {t : ℝ} (ht : t∈s) (z : Phase R) : 0<readback (coframeJet R hR s p himage t) z := by
  rw [coframeJet_actual_value R hR s p himage ht z]
  exact inv_pos.mpr (profile_pos (matched_positive R hR _ _ (himage t ht z.1)) z.2.property)

def coframeTimeRate (R : ℝ) (hR : 0<R) (s : Set ℝ) (c : ℝ) (p : ℝ→Space R)
    (himage : ∀ t∈s,∀ X,actualMoments R (readback (p t)) X∈momentImage R) (t : ℝ) : Distribution R :=
  denominatorField R (parameterRatePath R hR s (fun τ => readback (p τ))
    (fun τ => c • SpatialCollision.collision R hR.le (readback (p τ))-advection R (p τ)) himage t)

theorem coframeTimeRate_actual_moments (R : ℝ) (hR : 0<R) (s : Set ℝ) (c : ℝ) (p : ℝ→Space R)
    (himage : ∀ t∈s,∀ X,actualMoments R (readback (p t)) X∈momentImage R)
    {t : ℝ} (ht : t∈s) (x : RealPosition) (k : MomentumDomain R) :
    coframeTimeRate R hR s c p himage t (torusQuotient x,k)=
      reciprocalProfile (matchedTimeRate R hR (p t) x) k := by
  have hm : actualMoments R
      (c • SpatialCollision.collision R hR.le (readback (p t))-advection R (p t))
      (torusQuotient x)=-divergenceVector R (p t) x := by
    ext i
    change spatialMoment R (basisParameter i)
      (c • SpatialCollision.collision R hR.le (readback (p t))-advection R (p t))
        (torusQuotient x)=-fluxDivergence R (basisParameter i) (p t) x
    simp only [map_sub,map_smul,spatial_collision_five_moments hR.le,smul_zero,zero_sub,
      ContinuousMap.neg_apply,moment_advection_eq_fluxDivergence]
  change reciprocalProfile (parameterRatePath R hR s _ _ himage t (torusQuotient x)) k=_
  rw [parameterRatePath_apply R hR s _ _ himage ht (torusQuotient x),hm]
  rfl

theorem coframe_material_rate (R : ℝ) (hR : 0<R) (s : Set ℝ) (c : ℝ) (p : ℝ→Space R)
    (himage : ∀ t∈s,∀ X,actualMoments R (readback (p t)) X∈momentImage R)
    {t : ℝ} (ht : t∈s) (x : RealPosition) (k : MomentumDomain R) :
    coframeTimeRate R hR s c p himage t (torusQuotient x,k)+
      advection R (coframeJet R hR s p himage t) (torusQuotient x,k)=
      reciprocalProfile (matchedMaterialParameter R hR (p t) x k) k := by
  have hq : realLift (readback (coframeJet R hR s p himage t))=
      fun y => denominatorCube R (matchedValue R hR (readback (p t)) (torusQuotient y)) := by
    rw [coframeJet_readback,denominatorField_realLift]
    funext y
    rw [parameterPath_apply R hR s _ himage ht (torusQuotient y)]
  have hθ := (matched_real_contDiffAt R hR (p t) x (himage t ht (torusQuotient x))).differentiableAt (by norm_num)
  have hd := (denominatorCube R).hasFDerivAt.comp x hθ.hasFDerivAt
  simp only [Function.comp_def] at hd
  rw [coframeTimeRate_actual_moments R hR s c p himage ht x k,
    advection_realLift R (coframeJet R hR s p himage t) x k,hq,hd.fderiv]
  change Entropy.denominator Entropy.fiveInvariants (matchedTimeRate R hR (p t) x) (coordinates k)+
    Entropy.denominator Entropy.fiveInvariants
      (matchedSpatialDerivative R hR (p t) x (velocity R k)) (coordinates k)=
    Entropy.denominator Entropy.fiveInvariants
      (matchedTimeRate R hR (p t) x+matchedSpatialDerivative R hR (p t) x (velocity R k)) (coordinates k)
  simp_rw [←denominatorCLM_apply]
  exact (map_add _ _ _).symm

theorem original_mild_coframe_strong_derivative {R T : ℝ} (hR : 0<R) (hT : 0≤T)
    (c : ℝ) (p₀ : Space R) (p : ℝ→Space R) (hp : ContinuousOn p (Icc 0 T))
    (he : ∀ t∈Icc 0 T,readback (p t)=transport R t (readback p₀)+
      ∫ s in (0 : ℝ)..t,c • transport R (t-s)
        (SpatialCollision.collision R hR.le (readback (p s))))
    (himage : ∀ t∈Icc 0 T,∀ X,actualMoments R (readback (p t)) X∈momentImage R)
    {t : ℝ} (ht : t∈Icc 0 T) :
    HasDerivWithinAt (fun τ => readback (coframeJet R hR (Icc 0 T) p himage τ))
      (coframeTimeRate R hR (Icc 0 T) c p himage t) (Icc 0 T) t := by
  simp only [coframeJet_readback]
  exact (denominatorField R).hasFDerivAt.comp_hasDerivWithinAt t
    (original_mild_matched_strong_derivative hR hT c p₀ p hp he himage ht)

/-- All weights in this energy identity are now constructed from the same
actual solution. The full time-dependent metric term is retained. -/
theorem original_mild_actual_coframe_h3_energy {R T : ℝ} (hR : 0<R) (hT : 0≤T)
    (c : ℝ) (p₀ : Space R) (p : ℝ→Space R) (hp : ContinuousOn p (Icc 0 T))
    (he : ∀ t∈Icc 0 T,readback (p t)=transport R t (readback p₀)+
      ∫ s in (0 : ℝ)..t,c • transport R (t-s)
        (SpatialCollision.collision R hR.le (readback (p s))))
    (himage : ∀ t∈Icc 0 T,∀ X,actualMoments R (readback (p t)) X∈momentImage R)
    {t : ℝ} (ht : t∈Icc 0 T) :
    HasDerivWithinAt (fun τ => JetEnergy.h3Energy R
        (readback (coframeJet R hR (Icc 0 T) p himage τ)*
          readback (coframeJet R hR (Icc 0 T) p himage τ)) (p τ))
      (JetEnergy.h3Energy R ((2:ℝ) • (readback (coframeJet R hR (Icc 0 T) p himage t)*
        (coframeTimeRate R hR (Icc 0 T) c p himage t+
          advection R (coframeJet R hR (Icc 0 T) p himage t)))) (p t)+
        c*JetEnergy.h3CollisionPairing R hR.le
          (readback (coframeJet R hR (Icc 0 T) p himage t)*
            readback (coframeJet R hR (Icc 0 T) p himage t)) (p t)) (Icc 0 T) t :=
  original_mild_low_regularity_weight_h3_energy hR.le hT c p₀ p hp he ht
    (original_mild_coframe_strong_derivative hR hT c p₀ p hp he himage ht)

#check denominatorField_realLift
#check actual_parameterPath_contDiff
#check coframeJet_readback
#check coframeJet_actual_value
#check coframeJet_positive
#check coframeTimeRate_actual_moments
#check coframe_material_rate
#check original_mild_coframe_strong_derivative
#check original_mild_actual_coframe_h3_energy
#print axioms denominatorField_realLift
#print axioms actual_parameterPath_contDiff
#print axioms coframeJet_readback
#print axioms coframeJet_actual_value
#print axioms coframeJet_positive
#print axioms coframeTimeRate_actual_moments
#print axioms coframe_material_rate
#print axioms original_mild_coframe_strong_derivative
#print axioms original_mild_actual_coframe_h3_energy

end
end Resonance.ActualCoframeWeight
