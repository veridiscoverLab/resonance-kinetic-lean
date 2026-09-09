import Resonance.JetLocalKinetics

/-! The actual solution satisfies Duhamel in the entire compatible spatial
jet space. Spatial differentiation is then a bounded linear extraction from
that same equation, not differentiation of an unrelated tensor evolution. -/
open Set MeasureTheory
open scoped Interval
namespace Resonance.JetMildEquation
noncomputable section
open JetCollision SpatialChainRule FreeTransport
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 30000

def transportedSource (R : ℝ) (hR : 0 ≤ R) (c t s : ℝ) (p : Space R) : Space R :=
  c • JetTransport.map R (t-s) (JetCollision.collision R hR p)

theorem transportedSource_continuous (R : ℝ) (hR : 0 ≤ R) (c t : ℝ)
    {p : ℝ → Space R} (hp : Continuous p) :
    Continuous (fun s => transportedSource R hR c t s (p s)) := by
  unfold transportedSource
  exact ((JetTransport.map_joint_continuous R).comp
    ((continuous_const.sub continuous_id).prodMk
      ((JetCollision.collision_contDiff R hR ⊤).continuous.comp hp))).const_smul c

theorem transportedSource_readback (R : ℝ) (hR : 0 ≤ R) (c t s : ℝ) (p : Space R) :
    readback (transportedSource R hR c t s p) =
      c • transport R (t-s) (SpatialCollision.collision R hR (readback p)) := by
  simp only [transportedSource,readback_smul,JetTransport.map_readback,collision_readback]

theorem readback_intervalIntegral {R a b : ℝ} {u : ℝ → Space R}
    (hu : IntervalIntegrable u volume a b) :
    readback (∫ s in a..b,u s) = ∫ s in a..b,readback (u s) :=
  (JetLocalKinetics.readbackOperator R).intervalIntegral_comp_comm hu |>.symm

/-- The hypothesis is precisely the original mild equation at this time.
The conclusion retains every derivative in one common Banach integral. -/
theorem actual_mild_to_jet_duhamel {R : ℝ} (hR : 0 ≤ R) (c t : ℝ)
    (p₀ : Space R) (p : ℝ → Space R) (hp : Continuous p)
    (he : readback (p t) = transport R t (readback p₀) +
      ∫ s in (0 : ℝ)..t,c • transport R (t-s) (SpatialCollision.collision R hR (readback (p s)))) :
    p t = JetTransport.map R t p₀ + ∫ s in (0 : ℝ)..t,transportedSource R hR c t s (p s) := by
  apply readback_injective R
  have hi : IntervalIntegrable (fun s => transportedSource R hR c t s (p s)) volume 0 t :=
    (transportedSource_continuous R hR c t hp).intervalIntegrable 0 t
  rw [readback_add,JetTransport.map_readback,readback_intervalIntegral hi]
  simpa only [transportedSource_readback] using he

theorem actual_mild_linear_extraction {R : ℝ} (hR : 0 ≤ R) (c t : ℝ)
    (p₀ : Space R) (p : ℝ → Space R) (hp : Continuous p)
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (L : Space R →L[ℝ] F)
    (he : readback (p t) = transport R t (readback p₀) +
      ∫ s in (0 : ℝ)..t,c • transport R (t-s) (SpatialCollision.collision R hR (readback (p s)))) :
    L (p t) = L (JetTransport.map R t p₀) +
      ∫ s in (0 : ℝ)..t,L (transportedSource R hR c t s (p s)) := by
  rw [actual_mild_to_jet_duhamel hR c t p₀ p hp he,map_add]
  rw [← L.intervalIntegral_comp_comm
    ((transportedSource_continuous R hR c t hp).intervalIntegrable 0 t)]

def valueAt (R : ℝ) (x : RealPosition) : Space R →L[ℝ] SpatialJetSpace.V0 R :=
  (JetTransport.evaluationCLM R (torusQuotient x)).comp (JetLocalKinetics.readbackOperator R)

def firstLinear (R : ℝ) (x : RealPosition) : Space R →ₗ[ℝ] SpatialJetSpace.V1 R where
  toFun p := p.val.2.1 (torusQuotient x)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem firstLinear_bound (R : ℝ) (x : RealPosition) (p : Space R) :
    ‖firstLinear R x p‖ ≤ ‖p‖ :=
  ((p.val.2.1).norm_coe_le_norm (torusQuotient x)).trans
    ((norm_fst_le p.val.2).trans (norm_snd_le p.val))

def firstAt (R : ℝ) (x : RealPosition) : Space R →L[ℝ] SpatialJetSpace.V1 R :=
  (firstLinear R x).mkContinuous 1 (fun p => by simpa only [one_mul] using firstLinear_bound R x p)

def secondLinear (R : ℝ) (x : RealPosition) : Space R →ₗ[ℝ] SpatialJetSpace.V2 R where
  toFun p := p.val.2.2.1 (torusQuotient x)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem secondLinear_bound (R : ℝ) (x : RealPosition) (p : Space R) :
    ‖secondLinear R x p‖ ≤ ‖p‖ :=
  ((p.val.2.2.1).norm_coe_le_norm (torusQuotient x)).trans
    ((norm_fst_le p.val.2.2).trans ((norm_snd_le p.val.2).trans (norm_snd_le p.val)))

def secondAt (R : ℝ) (x : RealPosition) : Space R →L[ℝ] SpatialJetSpace.V2 R :=
  (secondLinear R x).mkContinuous 1 (fun p => by simpa only [one_mul] using secondLinear_bound R x p)

def thirdLinear (R : ℝ) (x : RealPosition) : Space R →ₗ[ℝ] SpatialJetSpace.V3 R where
  toFun p := p.val.2.2.2 (torusQuotient x)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem thirdLinear_bound (R : ℝ) (x : RealPosition) (p : Space R) :
    ‖thirdLinear R x p‖ ≤ ‖p‖ :=
  ((p.val.2.2.2).norm_coe_le_norm (torusQuotient x)).trans
    ((norm_snd_le p.val.2.2).trans ((norm_snd_le p.val.2).trans (norm_snd_le p.val)))

def thirdAt (R : ℝ) (x : RealPosition) : Space R →L[ℝ] SpatialJetSpace.V3 R :=
  (thirdLinear R x).mkContinuous 1 (fun p => by simpa only [one_mul] using thirdLinear_bound R x p)

theorem valueAt_actual (R : ℝ) (x : RealPosition) (p : Space R) :
    valueAt R x p = realLift (readback p) x := rfl

theorem firstAt_actual (R : ℝ) (x : RealPosition) (p : Space R) :
    firstAt R x p = fderiv ℝ (realLift (readback p)) x :=
  (SpatialJetSpace.compatible_first_fderiv p.property x).symm

theorem secondAt_actual (R : ℝ) (x : RealPosition) (p : Space R) :
    secondAt R x p = fderiv ℝ (fderiv ℝ (realLift (readback p))) x :=
  (SpatialJetSpace.compatible_second_fderiv p.property x).symm

theorem thirdAt_actual (R : ℝ) (x : RealPosition) (p : Space R) :
    thirdAt R x p = fderiv ℝ (fderiv ℝ (fderiv ℝ (realLift (readback p)))) x :=
  (SpatialJetSpace.compatible_third_fderiv p.property x).symm

theorem first_derivative_duhamel {R : ℝ} (hR : 0 ≤ R) (c t : ℝ)
    (p₀ : Space R) (p : ℝ → Space R) (hp : Continuous p) (x : RealPosition)
    (he : readback (p t) = transport R t (readback p₀) +
      ∫ s in (0 : ℝ)..t,c • transport R (t-s) (SpatialCollision.collision R hR (readback (p s)))) :
    fderiv ℝ (realLift (readback (p t))) x =
      fderiv ℝ (realLift (transport R t (readback p₀))) x +
      ∫ s in (0 : ℝ)..t,fderiv ℝ (realLift
        (c • transport R (t-s) (SpatialCollision.collision R hR (readback (p s))))) x := by
  simpa only [firstAt_actual,JetTransport.map_readback,transportedSource_readback] using
    actual_mild_linear_extraction hR c t p₀ p hp (firstAt R x) he

theorem second_derivative_duhamel {R : ℝ} (hR : 0 ≤ R) (c t : ℝ)
    (p₀ : Space R) (p : ℝ → Space R) (hp : Continuous p) (x : RealPosition)
    (he : readback (p t) = transport R t (readback p₀) +
      ∫ s in (0 : ℝ)..t,c • transport R (t-s) (SpatialCollision.collision R hR (readback (p s)))) :
    fderiv ℝ (fderiv ℝ (realLift (readback (p t)))) x =
      fderiv ℝ (fderiv ℝ (realLift (transport R t (readback p₀)))) x +
      ∫ s in (0 : ℝ)..t,fderiv ℝ (fderiv ℝ (realLift
        (c • transport R (t-s) (SpatialCollision.collision R hR (readback (p s)))))) x := by
  simpa only [secondAt_actual,JetTransport.map_readback,transportedSource_readback] using
    actual_mild_linear_extraction hR c t p₀ p hp (secondAt R x) he

/-- All three spatial derivatives of the same full source remain under the
same physical-time integral. No momentum derivative is taken. -/
theorem third_derivative_duhamel {R : ℝ} (hR : 0 ≤ R) (c t : ℝ)
    (p₀ : Space R) (p : ℝ → Space R) (hp : Continuous p) (x : RealPosition)
    (he : readback (p t) = transport R t (readback p₀) +
      ∫ s in (0 : ℝ)..t,c • transport R (t-s) (SpatialCollision.collision R hR (readback (p s)))) :
    fderiv ℝ (fderiv ℝ (fderiv ℝ (realLift (readback (p t))))) x =
      fderiv ℝ (fderiv ℝ (fderiv ℝ (realLift (transport R t (readback p₀))))) x +
      ∫ s in (0 : ℝ)..t,fderiv ℝ (fderiv ℝ (fderiv ℝ (realLift
        (c • transport R (t-s) (SpatialCollision.collision R hR (readback (p s))))))) x := by
  simpa only [thirdAt_actual,JetTransport.map_readback,transportedSource_readback] using
    actual_mild_linear_extraction hR c t p₀ p hp (thirdAt R x) he

/-- Time differentiation in the original interaction picture, in the whole
compatible norm. The differential equation is derived from the integral. -/
theorem moving_frame_hasDerivWithinAt {R T : ℝ} (hR : 0 ≤ R) (hT : 0 ≤ T)
    (c : ℝ) (p₀ : Space R) (g : ℝ → Space R) (hg : ContinuousOn g (Icc 0 T))
    (he : ∀ t ∈ Icc 0 T,g t=p₀+∫ s in (0 : ℝ)..t,JetKineticField.field R hR c s (g s)) :
    ∀ t ∈ Icc 0 T,HasDerivWithinAt g (JetKineticField.field R hR c t (g t)) (Icc 0 T) t := by
  intro t ht
  apply (ODE.hasDerivWithinAt_picard_Icc (⟨le_rfl,hT⟩ : 0 ∈ Icc 0 T)
    (u := Set.univ) (JetKineticField.field_joint_continuous R hR c).continuousOn hg
    (fun _ _ => Set.mem_univ _) p₀ ht).congr_of_mem _ ht
  intro s hs
  exact he s hs

end
end Resonance.JetMildEquation

#check Resonance.JetMildEquation.transportedSource_continuous
#print axioms Resonance.JetMildEquation.transportedSource_continuous
#check Resonance.JetMildEquation.transportedSource_readback
#print axioms Resonance.JetMildEquation.transportedSource_readback
#check Resonance.JetMildEquation.readback_intervalIntegral
#print axioms Resonance.JetMildEquation.readback_intervalIntegral
#check Resonance.JetMildEquation.actual_mild_to_jet_duhamel
#print axioms Resonance.JetMildEquation.actual_mild_to_jet_duhamel
#check Resonance.JetMildEquation.actual_mild_linear_extraction
#print axioms Resonance.JetMildEquation.actual_mild_linear_extraction
#check Resonance.JetMildEquation.firstLinear_bound
#print axioms Resonance.JetMildEquation.firstLinear_bound
#check Resonance.JetMildEquation.secondLinear_bound
#print axioms Resonance.JetMildEquation.secondLinear_bound
#check Resonance.JetMildEquation.thirdLinear_bound
#print axioms Resonance.JetMildEquation.thirdLinear_bound
#check Resonance.JetMildEquation.valueAt_actual
#print axioms Resonance.JetMildEquation.valueAt_actual
#check Resonance.JetMildEquation.firstAt_actual
#print axioms Resonance.JetMildEquation.firstAt_actual
#check Resonance.JetMildEquation.secondAt_actual
#print axioms Resonance.JetMildEquation.secondAt_actual
#check Resonance.JetMildEquation.thirdAt_actual
#print axioms Resonance.JetMildEquation.thirdAt_actual
#check Resonance.JetMildEquation.first_derivative_duhamel
#print axioms Resonance.JetMildEquation.first_derivative_duhamel
#check Resonance.JetMildEquation.second_derivative_duhamel
#print axioms Resonance.JetMildEquation.second_derivative_duhamel
#check Resonance.JetMildEquation.third_derivative_duhamel
#print axioms Resonance.JetMildEquation.third_derivative_duhamel
#check Resonance.JetMildEquation.moving_frame_hasDerivWithinAt
#print axioms Resonance.JetMildEquation.moving_frame_hasDerivWithinAt
