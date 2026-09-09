import Resonance.JetEnergy
import Resonance.JetAmplitudeBounds
import Mathlib.Analysis.Calculus.Deriv.Slope

/-! The true velocity derivative of a compatible spatial jet, followed along
the original characteristics. No momentum differentiability is required. -/
open Set MeasureTheory
open Filter
open scoped Topology
namespace Resonance.TransportMaterialDerivative
noncomputable section
open FreeTransport JetCollision SpatialChainRule SpatialJetSpace SpatialTranslationOrbit
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 30000

section Evaluation
variable {K : Type*} [TopologicalSpace K] [CompactSpace K]
theorem hasDerivAt_of_evaluations {u D : ℝ → C(K,ℝ)} {t : ℝ}
    (hD : ContinuousAt D t) (hu : ∀ s k,HasDerivAt (fun τ => u τ k) (D s k) s) :
    HasDerivAt u (D t) t := by
  apply hasDerivAt_iff_hasFDerivAt.mpr
  apply UniformEvaluationDerivative.hasFDerivAt_of_evaluations
    (A := fun s => ContinuousLinearMap.toSpanSingleton ℝ (D s))
  · exact ((ContinuousLinearMap.smulRightL ℝ ℝ C(K,ℝ) (1 : ℝ →L[ℝ] ℝ)).continuous.continuousAt.comp hD)
  · intro s k
    convert (hu s k).hasFDerivAt using 1
end Evaluation

def velocity (R : ℝ) (k : MomentumDomain R) : RealPosition := fun j => 2*(k:ResonantMeasure.E) j

def advection (R : ℝ) (p : Space R) : Distribution R :=
  ⟨fun z => p.val.2.1 z.1 (velocity R z.2) z.2, by
    have hA : Continuous (fun z : Phase R => p.val.2.1 z.1) := p.val.2.1.continuous.comp continuous_fst
    have hv : Continuous (fun z : Phase R => velocity R z.2) := by
      unfold velocity
      apply continuous_pi
      intro j
      fun_prop
    exact Continuous.eval (hA.clm_apply hv) continuous_snd⟩

theorem characteristic_lift (R t : ℝ) (a : RealPosition) (k : MomentumDomain R) :
    characteristic (-t) (torusQuotient a,k) =
      (torusQuotient (a+t • velocity R k),k) := by
  apply Prod.ext
  · ext j
    change (a j : AddCircle period)-((2*(-t)*(k:ResonantMeasure.E) j:ℝ):AddCircle period)=
      ((a j+t*(2*(k:ResonantMeasure.E) j):ℝ):AddCircle period)
    rw [←AddCircle.coe_sub]
    congr 1
    ring
  · rfl

theorem transport_evaluation_hasDerivAt (R : ℝ) (p : Space R) (t : ℝ) (z : Phase R) :
    HasDerivAt (fun τ => transport R (-τ) (readback p) z)
      (transport R (-t) (advection R p) z) t := by
  obtain ⟨a,ha⟩ := torusQuotient_surjective z.1
  have hz : z=(torusQuotient a,z.2) := Prod.ext ha.symm rfl
  rw [hz]
  have hx : HasDerivAt (fun τ : ℝ => a+τ • velocity R z.2) (velocity R z.2) t := by
    simpa only [one_smul] using (hasDerivAt_id t).smul_const (velocity R z.2) |>.const_add a
  have hp := (p.property.1 (a+t • velocity R z.2)).comp_hasDerivAt t hx
  have h := (ContinuousMap.evalCLM (R := ℝ) z.2).hasFDerivAt.comp_hasDerivAt t hp
  have he : (fun τ => transport R (-τ) (readback p) (torusQuotient a,z.2)) =
      fun τ => fieldLift p.val.1 (a+τ • velocity R z.2) z.2 := by
    funext τ
    rw [transport_apply,characteristic_lift]
    rfl
  rw [he]
  convert h using 1
  rw [transport_apply,characteristic_lift]
  rfl

/-- Genuine supremum-norm time differentiation, uniform over the entire
closed physical phase space. -/
theorem transport_hasDerivAt (R : ℝ) (p : Space R) (t : ℝ) :
    HasDerivAt (fun τ => transport R (-τ) (readback p))
      (transport R (-t) (advection R p)) t := by
  apply hasDerivAt_of_evaluations (D := fun τ => transport R (-τ) (advection R p))
  · exact ((transport_strong_continuous R (advection R p)).comp continuous_neg).continuousAt
  · exact fun s z => transport_evaluation_hasDerivAt R p s z

section StrongFamily
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- A strong, jointly continuous operator family suffices. No operator-norm
derivative is assumed, and the difference quotient keeps the common time. -/
theorem strong_family_hasDerivWithinAt (A : ℝ → E →L[ℝ] F)
    (hA : Continuous (fun q : ℝ × E => A q.1 q.2))
    {p : ℝ → E} {p' : E} {t : ℝ} {s : Set ℝ} {b : F}
    (hp : HasDerivWithinAt p p' s t)
    (hfixed : HasDerivWithinAt (fun τ => A τ (p t)) b s t) :
    HasDerivWithinAt (fun τ => A τ (p τ)) (A t p'+b) s t := by
  rw [hasDerivWithinAt_iff_tendsto_slope] at hp hfixed ⊢
  have hlim := (hA.tendsto (t,p')).comp
    ((continuousAt_id.mono_left nhdsWithin_le_nhds).prodMk_nhds hp)
  have hsum := hlim.add hfixed
  apply hsum.congr'
  apply Filter.Eventually.of_forall
  intro τ
  simp only [slope,Function.comp_apply,id_eq,vsub_eq_sub,map_smul,map_sub]
  rw [←smul_add]
  congr 1
  abel
end StrongFamily

def movingReadback (R t : ℝ) : Space R →L[ℝ] Distribution R :=
  (transportCLM R (-t)).comp (JetLocalKinetics.readbackOperator R)

theorem movingReadback_joint_continuous (R : ℝ) :
    Continuous (fun q : ℝ × Space R => movingReadback R q.1 q.2) := by
  have h := (JetLocalKinetics.readbackOperator R).continuous.comp
    ((JetTransport.map_joint_continuous R).comp
      ((continuous_fst.neg).prodMk continuous_snd))
  simpa only [JetTransport.map_readback] using h

/-- The full material derivative of an actual time-dependent compatible
weight path, including all three original velocity components. -/
theorem material_hasDerivWithinAt (R : ℝ) {w : ℝ → Space R} {w' : Space R}
    {s : Set ℝ} {t : ℝ} (hw : HasDerivWithinAt w w' s t) :
    HasDerivWithinAt (fun τ => transport R (-τ) (readback (w τ)))
      (transport R (-t) (readback w'+advection R (w t))) s t := by
  have h := strong_family_hasDerivWithinAt (movingReadback R)
    (movingReadback_joint_continuous R) hw
    (transport_hasDerivAt R (w t) t).hasDerivWithinAt
  simpa only [movingReadback,ContinuousLinearMap.comp_apply,FreeTransport.transport_add] using h

theorem advection_realLift (R : ℝ) (p : Space R) (a : RealPosition)
    (k : MomentumDomain R) :
    advection R p (torusQuotient a,k) =
      fderiv ℝ (realLift (readback p)) a (velocity R k) k := by
  change p.val.2.1 (torusQuotient a) (velocity R k) k =
    fderiv ℝ (fieldLift p.val.1) a (velocity R k) k
  rw [SpatialJetSpace.compatible_first_fderiv p.property a]

/-- The inverse-square RJ weight is q², with q=1/N. Its complete
material derivative is 2q Dq; there is no dropped time-dependent metric term. -/
theorem squared_weight_material_derivative (R : ℝ) {q : ℝ → Space R} {q' : Space R}
    {s : Set ℝ} {t : ℝ} (hq : HasDerivWithinAt q q' s t) :
    HasDerivWithinAt (fun τ => transport R (-τ) (readback (q τ)*readback (q τ)))
      (transport R (-t) ((2:ℝ) • (readback (q t)*(readback q'+advection R (q t))))) s t := by
  have h := (material_hasDerivWithinAt R hq).mul (material_hasDerivWithinAt R hq)
  simp only [←PhaseEnergy.transport_mul,←FreeTransport.transport_add] at h
  have hr : (readback q'+advection R (q t))*readback (q t)+
      readback (q t)*(readback q'+advection R (q t)) =
      (2:ℝ) • (readback (q t)*(readback q'+advection R (q t))) := by
    ext z
    simp only [ContinuousMap.mul_apply,ContinuousMap.add_apply,ContinuousMap.smul_apply,smul_eq_mul]
    ring
  rw [hr] at h
  exact h

/-- Actual H³ energy with an independently supplied C¹ compatible weight
path. The material derivative input of JetEnergy is now fully discharged. -/
theorem actual_weight_h3_energy {R T : ℝ} (hR : 0 ≤ R) (hT : 0 ≤ T)
    (c : ℝ) (p₀ : Space R) (g : ℝ → Space R) (hg : ContinuousOn g (Icc 0 T))
    (he : ∀ t ∈ Icc 0 T,g t=p₀+∫ s in (0 : ℝ)..t,JetKineticField.field R hR c s (g s))
    {q : ℝ → Space R} {q' : Space R} {t : ℝ} (ht : t ∈ Icc 0 T)
    (hq : HasDerivWithinAt q q' (Icc 0 T) t) :
    HasDerivWithinAt
      (fun τ => JetEnergy.h3Energy R (readback (q τ)*readback (q τ)) (JetTransport.map R τ (g τ)))
      (JetEnergy.h3Energy R ((2:ℝ) • (readback (q t)*(readback q'+advection R (q t))))
          (JetTransport.map R t (g t))+
        c*JetEnergy.h3CollisionPairing R hR (readback (q t)*readback (q t))
          (JetTransport.map R t (g t))) (Icc 0 T) t :=
  JetEnergy.physical_h3_energy_derivative hR hT c p₀ g hg he ht
    (squared_weight_material_derivative R hq)

/-- The hypothesis is the original C(phase) mild equation, not a separately
postulated higher-order differential system. -/
theorem original_mild_squared_weight_h3_energy {R T : ℝ} (hR : 0 ≤ R) (hT : 0 ≤ T)
    (c : ℝ) (p₀ : Space R) (p : ℝ → Space R) (hp : ContinuousOn p (Icc 0 T))
    (he : ∀ t ∈ Icc 0 T,readback (p t)=transport R t (readback p₀)+
      ∫ s in (0 : ℝ)..t,c • transport R (t-s)
        (SpatialCollision.collision R hR (readback (p s))))
    {q : ℝ → Space R} {q' : Space R} {t : ℝ} (ht : t ∈ Icc 0 T)
    (hq : HasDerivWithinAt q q' (Icc 0 T) t) :
    HasDerivWithinAt (fun τ => JetEnergy.h3Energy R (readback (q τ)*readback (q τ)) (p τ))
      (JetEnergy.h3Energy R ((2:ℝ) • (readback (q t)*(readback q'+advection R (q t)))) (p t)+
        c*JetEnergy.h3CollisionPairing R hR (readback (q t)*readback (q t)) (p t)) (Icc 0 T) t := by
  have h := actual_weight_h3_energy hR hT c p₀ (JetAmplitudeBounds.toFrame R p)
    (JetAmplitudeBounds.toFrame_continuousOn hp)
    (JetAmplitudeBounds.actual_mild_to_moving_frame hR c p₀ p hp he) ht hq
  simpa only [JetAmplitudeBounds.toFrame,JetTransport.map_add_time,add_neg_cancel,
    JetTransport.map_zero_time] using h

/-- The material formula requires only a C(phase)-valued time derivative.
In particular, no spatial derivative of the time derivative is assumed. -/
theorem material_readback_hasDerivWithinAt (R : ℝ) {q : ℝ → Space R}
    {q' : Distribution R} {s : Set ℝ} {t : ℝ}
    (hq : HasDerivWithinAt (fun τ => readback (q τ)) q' s t) :
    HasDerivWithinAt (fun τ => transport R (-τ) (readback (q τ)))
      (transport R (-t) (q'+advection R (q t))) s t := by
  have hA : Continuous (fun z : ℝ × Distribution R => transportCLM R (-z.1) z.2) :=
    (TransportDuhamel.transport_joint_continuous R).comp (continuous_fst.neg.prodMk continuous_snd)
  have h := strong_family_hasDerivWithinAt (fun τ => transportCLM R (-τ)) hA hq
    (transport_hasDerivAt R (q t) t).hasDerivWithinAt
  simpa only [FreeTransport.transport_add] using h

theorem squared_weight_readback_derivative (R : ℝ) {q : ℝ → Space R}
    {q' : Distribution R} {s : Set ℝ} {t : ℝ}
    (hq : HasDerivWithinAt (fun τ => readback (q τ)) q' s t) :
    HasDerivWithinAt (fun τ => transport R (-τ) (readback (q τ)*readback (q τ)))
      (transport R (-t) ((2:ℝ) • (readback (q t)*(q'+advection R (q t))))) s t := by
  have h := (material_readback_hasDerivWithinAt R hq).mul
    (material_readback_hasDerivWithinAt R hq)
  simp only [←PhaseEnergy.transport_mul,←FreeTransport.transport_add] at h
  have hr : (q'+advection R (q t))*readback (q t)+readback (q t)*(q'+advection R (q t)) =
      (2:ℝ) • (readback (q t)*(q'+advection R (q t))) := by
    ext z
    simp only [ContinuousMap.mul_apply,ContinuousMap.add_apply,ContinuousMap.smul_apply,smul_eq_mul]
    ring
  rw [hr] at h
  exact h

/-- The actual original mild solution with a spatially compatible weight,
whose time derivative exists only in C(phase). This is the energy interface
that does not spend an extra spatial derivative of the actual moment path. -/
theorem original_mild_low_regularity_weight_h3_energy {R T : ℝ}
    (hR : 0 ≤ R) (hT : 0 ≤ T) (c : ℝ) (p₀ : Space R) (p : ℝ → Space R)
    (hp : ContinuousOn p (Icc 0 T))
    (he : ∀ t ∈ Icc 0 T,readback (p t)=transport R t (readback p₀)+
      ∫ s in (0 : ℝ)..t,c • transport R (t-s)
        (SpatialCollision.collision R hR (readback (p s))))
    {q : ℝ → Space R} {q' : Distribution R} {t : ℝ} (ht : t ∈ Icc 0 T)
    (hq : HasDerivWithinAt (fun τ => readback (q τ)) q' (Icc 0 T) t) :
    HasDerivWithinAt (fun τ => JetEnergy.h3Energy R (readback (q τ)*readback (q τ)) (p τ))
      (JetEnergy.h3Energy R ((2:ℝ) • (readback (q t)*(q'+advection R (q t)))) (p t)+
        c*JetEnergy.h3CollisionPairing R hR (readback (q t)*readback (q t)) (p t)) (Icc 0 T) t := by
  have h := JetEnergy.physical_h3_energy_derivative hR hT c p₀ (JetAmplitudeBounds.toFrame R p)
    (JetAmplitudeBounds.toFrame_continuousOn hp)
    (JetAmplitudeBounds.actual_mild_to_moving_frame hR c p₀ p hp he) ht
    (squared_weight_readback_derivative R hq)
  simpa only [JetAmplitudeBounds.toFrame,JetTransport.map_add_time,add_neg_cancel,
    JetTransport.map_zero_time] using h

end
end Resonance.TransportMaterialDerivative

#check Resonance.TransportMaterialDerivative.hasDerivAt_of_evaluations
#print axioms Resonance.TransportMaterialDerivative.hasDerivAt_of_evaluations
#check Resonance.TransportMaterialDerivative.characteristic_lift
#print axioms Resonance.TransportMaterialDerivative.characteristic_lift
#check Resonance.TransportMaterialDerivative.transport_evaluation_hasDerivAt
#print axioms Resonance.TransportMaterialDerivative.transport_evaluation_hasDerivAt
#check Resonance.TransportMaterialDerivative.transport_hasDerivAt
#print axioms Resonance.TransportMaterialDerivative.transport_hasDerivAt
#check Resonance.TransportMaterialDerivative.strong_family_hasDerivWithinAt
#print axioms Resonance.TransportMaterialDerivative.strong_family_hasDerivWithinAt
#check Resonance.TransportMaterialDerivative.movingReadback_joint_continuous
#print axioms Resonance.TransportMaterialDerivative.movingReadback_joint_continuous
#check Resonance.TransportMaterialDerivative.material_hasDerivWithinAt
#print axioms Resonance.TransportMaterialDerivative.material_hasDerivWithinAt
#check Resonance.TransportMaterialDerivative.advection_realLift
#print axioms Resonance.TransportMaterialDerivative.advection_realLift
#check Resonance.TransportMaterialDerivative.squared_weight_material_derivative
#print axioms Resonance.TransportMaterialDerivative.squared_weight_material_derivative
#check Resonance.TransportMaterialDerivative.actual_weight_h3_energy
#print axioms Resonance.TransportMaterialDerivative.actual_weight_h3_energy
#check Resonance.TransportMaterialDerivative.original_mild_squared_weight_h3_energy
#print axioms Resonance.TransportMaterialDerivative.original_mild_squared_weight_h3_energy

#check Resonance.TransportMaterialDerivative.material_readback_hasDerivWithinAt
#print axioms Resonance.TransportMaterialDerivative.material_readback_hasDerivWithinAt
#check Resonance.TransportMaterialDerivative.squared_weight_readback_derivative
#print axioms Resonance.TransportMaterialDerivative.squared_weight_readback_derivative
#check Resonance.TransportMaterialDerivative.original_mild_low_regularity_weight_h3_energy
#print axioms Resonance.TransportMaterialDerivative.original_mild_low_regularity_weight_h3_energy
