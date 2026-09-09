import Resonance.TransportMaterialDerivative

/-! The relative H³ identity compares the same actual mild solution with a
specified compatible reference path. The reference residual is computed from
that path; its smallness is neither assumed as a field nor asserted here. -/
open Set MeasureTheory
namespace Resonance.JetRelativeEnergy
noncomputable section
open FreeTransport JetCollision SpatialChainRule JetSeminorm PhaseEnergy JetEnergy
open TransportMaterialDerivative
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 30000

def pairing (R : ℝ) (n : ℕ) (hn : n ≤ 3) (v : Fin n → RealPosition)
    (w : Distribution R) (p q : Space R) : ℝ :=
  integralCLM R (w*(spatialDerivative R n hn v p*spatialDerivative R n hn v q))

theorem pairing_sub_right (R : ℝ) (n : ℕ) (hn : n ≤ 3) (v : Fin n → RealPosition)
    (w : Distribution R) (p q r : Space R) :
    pairing R n hn v w p (q-r)=pairing R n hn v w p q-pairing R n hn v w p r := by
  simp only [pairing,map_sub,mul_sub]

theorem pairing_smul_right (R : ℝ) (n : ℕ) (hn : n ≤ 3) (v : Fin n → RealPosition)
    (w : Distribution R) (p q : Space R) (c : ℝ) :
    pairing R n hn v w p (c • q)=c*pairing R n hn v w p q := by
  simp only [pairing,map_smul,mul_smul_comm,smul_eq_mul]

def h3Pairing (R : ℝ) (w : Distribution R) (p q : Space R) : ℝ :=
  ∑ a : SpatialIndex,pairing R a.1.val (by omega) (coordinateDirections a) w p q

/-- Exact identity for any C¹ moving path and its actual material velocity.
It is used below with the difference of the kinetic and reference paths. -/
theorem physical_path_energy_derivative (R : ℝ)
    {s : Set ℝ} {t : ℝ} {g : ℝ → Space R} {g' : Space R}
    (ht : t ∈ s) (hg : HasDerivWithinAt g g' s t)
    (n : ℕ) (hn : n ≤ 3) (v : Fin n → RealPosition)
    {w : ℝ → Distribution R} {b : Distribution R}
    (hw : HasDerivWithinAt (fun τ => transport R (-τ) (w τ)) (transport R (-t) b) s t) :
    HasDerivWithinAt
      (fun τ => derivativeEnergy R n hn v (w τ) (JetTransport.map R τ (g τ)))
      (derivativeEnergy R n hn v b (JetTransport.map R t (g t))+
        pairing R n hn v (w t) (JetTransport.map R t (g t)) (JetTransport.map R t g')) s t := by
  have hd := (spatialDerivative R n hn v).hasFDerivAt.comp_hasDerivWithinAt t hg
  have h := quadratic_hasDerivWithinAt R hw hd
  change HasDerivWithinAt _
    (quadratic R (transport R (-t) b) (spatialDerivative R n hn v (g t))+
      integralCLM R (transport R (-t) (w t)*
        (spatialDerivative R n hn v (g t)*spatialDerivative R n hn v g'))) s t at h
  rw [quadratic_moving_to_physical,←spatialDerivative_transport] at h
  have hx := triple_transport R t (transport R (-t) (w t))
    (spatialDerivative R n hn v (g t)) (spatialDerivative R n hn v g')
  rw [transport_add_time,add_neg_cancel,transport_zero,
    ←spatialDerivative_transport,←spatialDerivative_transport] at hx
  rw [←hx] at h
  apply h.congr_of_mem ?_ ht
  intro τ _
  unfold derivativeEnergy
  rw [quadratic_moving_to_physical,spatialDerivative_transport]
  rfl

def referenceResidual (R : ℝ) (hR : 0 ≤ R) (c t : ℝ) (b b' : Space R) : Space R :=
  JetTransport.map R t b' - c • JetCollision.collision R hR (JetTransport.map R t b)

theorem transport_difference (R t : ℝ) (p q : Space R) :
    JetTransport.map R t (p-q)=JetTransport.map R t p-JetTransport.map R t q :=
  (JetTransport.operator R t).map_sub p q

theorem transport_field (R : ℝ) (hR : 0 ≤ R) (c t : ℝ) (g : Space R) :
    JetTransport.map R t (JetKineticField.field R hR c t g) =
      c • JetCollision.collision R hR (JetTransport.map R t g) := by
  rw [JetKineticField.field,JetTransport.map_smul,JetTransport.map_add_time,
    add_neg_cancel,JetTransport.map_zero_time]

/-- The defect of the given reference appears with its exact minus sign;
the actual collision difference keeps all original parents. -/
theorem relative_material_source (R : ℝ) (hR : 0 ≤ R) (c t : ℝ) (g b b' : Space R) :
    JetTransport.map R t (JetKineticField.field R hR c t g-b') =
      c • (JetCollision.collision R hR (JetTransport.map R t g)-
        JetCollision.collision R hR (JetTransport.map R t b))-
          referenceResidual R hR c t b b' := by
  rw [transport_difference,transport_field,referenceResidual,smul_sub]
  abel

theorem physical_relative_energy_derivative {R T : ℝ} (hR : 0 ≤ R) (hT : 0 ≤ T)
    (c : ℝ) (p₀ : Space R) (g : ℝ → Space R) (hg : ContinuousOn g (Icc 0 T))
    (he : ∀ t ∈ Icc 0 T,g t=p₀+∫ s in (0 : ℝ)..t,JetKineticField.field R hR c s (g s))
    {b : ℝ → Space R} {b' : Space R} {t : ℝ} (ht : t ∈ Icc 0 T)
    (hb : HasDerivWithinAt b b' (Icc 0 T) t)
    (n : ℕ) (hn : n ≤ 3) (v : Fin n → RealPosition)
    {w : ℝ → Distribution R} {w' : Distribution R}
    (hw : HasDerivWithinAt (fun τ => transport R (-τ) (w τ)) (transport R (-t) w') (Icc 0 T) t) :
    HasDerivWithinAt
      (fun τ => derivativeEnergy R n hn v (w τ)
        (JetTransport.map R τ (g τ)-JetTransport.map R τ (b τ)))
      (derivativeEnergy R n hn v w' (JetTransport.map R t (g t)-JetTransport.map R t (b t))+
        c*pairing R n hn v (w t) (JetTransport.map R t (g t)-JetTransport.map R t (b t))
          (JetCollision.collision R hR (JetTransport.map R t (g t))-
            JetCollision.collision R hR (JetTransport.map R t (b t)))-
        pairing R n hn v (w t) (JetTransport.map R t (g t)-JetTransport.map R t (b t))
          (referenceResidual R hR c t (b t) b')) (Icc 0 T) t := by
  have h := physical_path_energy_derivative R ht
    ((JetMildEquation.moving_frame_hasDerivWithinAt hR hT c p₀ g hg he t ht).sub hb) n hn v hw
  simp only [Pi.sub_apply] at h
  rw [relative_material_source] at h
  simpa only [transport_difference,pairing_sub_right,pairing_smul_right,add_sub_assoc] using h

theorem physical_relative_h3_energy_derivative {R T : ℝ} (hR : 0 ≤ R) (hT : 0 ≤ T)
    (c : ℝ) (p₀ : Space R) (g : ℝ → Space R) (hg : ContinuousOn g (Icc 0 T))
    (he : ∀ t ∈ Icc 0 T,g t=p₀+∫ s in (0 : ℝ)..t,JetKineticField.field R hR c s (g s))
    {b : ℝ → Space R} {b' : Space R} {t : ℝ} (ht : t ∈ Icc 0 T)
    (hb : HasDerivWithinAt b b' (Icc 0 T) t)
    {w : ℝ → Distribution R} {w' : Distribution R}
    (hw : HasDerivWithinAt (fun τ => transport R (-τ) (w τ)) (transport R (-t) w') (Icc 0 T) t) :
    HasDerivWithinAt
      (fun τ => h3Energy R (w τ) (JetTransport.map R τ (g τ)-JetTransport.map R τ (b τ)))
      (h3Energy R w' (JetTransport.map R t (g t)-JetTransport.map R t (b t))+
        c*h3Pairing R (w t) (JetTransport.map R t (g t)-JetTransport.map R t (b t))
          (JetCollision.collision R hR (JetTransport.map R t (g t))-
            JetCollision.collision R hR (JetTransport.map R t (b t)))-
        h3Pairing R (w t) (JetTransport.map R t (g t)-JetTransport.map R t (b t))
          (referenceResidual R hR c t (b t) b')) (Icc 0 T) t := by
  have h := HasDerivWithinAt.sum (u := Finset.univ)
    (fun a _ => physical_relative_energy_derivative hR hT c p₀ g hg he ht hb
      a.1.val (by omega) (coordinateDirections a) hw)
  simpa only [h3Energy,h3Pairing,Finset.sum_sub_distrib,Finset.sum_add_distrib,Finset.mul_sum] using h

/-- Relative energy of the original mild solution. The reference is a known
C¹ moving-frame C³ path; the reciprocal weight needs only a C⁰ time derivative.
The reference residual is the actual computed defect, without a size premise. -/
theorem original_mild_relative_h3_energy {R T : ℝ} (hR : 0 ≤ R) (hT : 0 ≤ T)
    (c : ℝ) (p₀ : Space R) (p : ℝ → Space R) (hp : ContinuousOn p (Icc 0 T))
    (he : ∀ t ∈ Icc 0 T,readback (p t)=transport R t (readback p₀)+
      ∫ s in (0 : ℝ)..t,c • transport R (t-s)
        (SpatialCollision.collision R hR (readback (p s))))
    {b : ℝ → Space R} {b' : Space R} {t : ℝ} (ht : t ∈ Icc 0 T)
    (hb : HasDerivWithinAt b b' (Icc 0 T) t)
    {q : ℝ → Space R} {q' : Distribution R}
    (hq : HasDerivWithinAt (fun τ => readback (q τ)) q' (Icc 0 T) t) :
    HasDerivWithinAt
      (fun τ => h3Energy R (readback (q τ)*readback (q τ)) (p τ-JetTransport.map R τ (b τ)))
      (h3Energy R ((2:ℝ) • (readback (q t)*(q'+advection R (q t))))
          (p t-JetTransport.map R t (b t))+
        c*h3Pairing R (readback (q t)*readback (q t)) (p t-JetTransport.map R t (b t))
          (JetCollision.collision R hR (p t)-JetCollision.collision R hR (JetTransport.map R t (b t)))-
        h3Pairing R (readback (q t)*readback (q t)) (p t-JetTransport.map R t (b t))
          (referenceResidual R hR c t (b t) b')) (Icc 0 T) t := by
  have h := physical_relative_h3_energy_derivative hR hT c p₀ (JetAmplitudeBounds.toFrame R p)
    (JetAmplitudeBounds.toFrame_continuousOn hp)
    (JetAmplitudeBounds.actual_mild_to_moving_frame hR c p₀ p hp he) ht hb
    (squared_weight_readback_derivative R hq)
  simpa only [JetAmplitudeBounds.toFrame,JetTransport.map_add_time,add_neg_cancel,
    JetTransport.map_zero_time] using h

end
end Resonance.JetRelativeEnergy

#check Resonance.JetRelativeEnergy.pairing_sub_right
#print axioms Resonance.JetRelativeEnergy.pairing_sub_right
#check Resonance.JetRelativeEnergy.pairing_smul_right
#print axioms Resonance.JetRelativeEnergy.pairing_smul_right
#check Resonance.JetRelativeEnergy.physical_path_energy_derivative
#print axioms Resonance.JetRelativeEnergy.physical_path_energy_derivative
#check Resonance.JetRelativeEnergy.transport_difference
#print axioms Resonance.JetRelativeEnergy.transport_difference
#check Resonance.JetRelativeEnergy.transport_field
#print axioms Resonance.JetRelativeEnergy.transport_field
#check Resonance.JetRelativeEnergy.relative_material_source
#print axioms Resonance.JetRelativeEnergy.relative_material_source
#check Resonance.JetRelativeEnergy.physical_relative_energy_derivative
#print axioms Resonance.JetRelativeEnergy.physical_relative_energy_derivative
#check Resonance.JetRelativeEnergy.physical_relative_h3_energy_derivative
#print axioms Resonance.JetRelativeEnergy.physical_relative_h3_energy_derivative
#check Resonance.JetRelativeEnergy.original_mild_relative_h3_energy
#print axioms Resonance.JetRelativeEnergy.original_mild_relative_h3_energy
