import Resonance.PhaseEnergy
import Resonance.JetSeminorm

/-! Exact weighted spatial-derivative energy of the original mild solution.
All differentiations take place in the same compatible moving-frame path. -/
open Set MeasureTheory
namespace Resonance.JetEnergy
noncomputable section
open FreeTransport JetCollision SpatialChainRule JetSeminorm PhaseEnergy
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 30000

def tensorEvaluation (R : ℝ) (n : ℕ) (v : Fin n → RealPosition) :
    Tensor R n →L[ℝ] Distribution R :=
  ({toFun := fun A => A v
    map_add' := fun _ _ => rfl
    map_smul' := fun _ _ => rfl} : Tensor R n →ₗ[ℝ] Distribution R).mkContinuous
    (∏ i,‖v i‖) (fun A => by simpa only [mul_comm] using A.le_opNorm v)

def spatialDerivative (R : ℝ) (n : ℕ) (hn : n ≤ 3) (v : Fin n → RealPosition) :
    Space R →L[ℝ] Distribution R :=
  (tensorEvaluation R n v).comp (orbitDerivative R n hn)

theorem spatialDerivative_actual (R : ℝ) (n : ℕ) (hn : n ≤ 3)
    (v : Fin n → RealPosition) (p : Space R) :
    spatialDerivative R n hn v p =
      iteratedFDeriv ℝ n (SpatialTranslationOrbit.distributionOrbit (readback p)) 0 v := rfl

theorem spatialDerivative_transport (R t : ℝ) (n : ℕ) (hn : n ≤ 3)
    (v : Fin n → RealPosition) (p : Space R) :
    spatialDerivative R n hn v (JetTransport.map R t p) =
      transport R t (spatialDerivative R n hn v p) := by
  change orbitDerivative R n hn (JetTransport.map R t p) v = _
  rw [orbitDerivative_transport]
  rfl

def derivativeEnergy (R : ℝ) (n : ℕ) (hn : n ≤ 3)
    (v : Fin n → RealPosition) (w : Distribution R) (p : Space R) : ℝ :=
  quadratic R w (spatialDerivative R n hn v p)

theorem derivativeEnergy_transport (R t : ℝ) (n : ℕ) (hn : n ≤ 3)
    (v : Fin n → RealPosition) (w : Distribution R) (p : Space R) :
    derivativeEnergy R n hn v (transport R t w) (JetTransport.map R t p) =
      derivativeEnergy R n hn v w p := by
  unfold derivativeEnergy
  rw [spatialDerivative_transport,quadratic_transport]

theorem field_spatialDerivative (R : ℝ) (hR : 0 ≤ R) (c t : ℝ)
    (n : ℕ) (hn : n ≤ 3) (v : Fin n → RealPosition) (g : Space R) :
    spatialDerivative R n hn v (JetKineticField.field R hR c t g) =
      c • transport R (-t) (spatialDerivative R n hn v
        (JetCollision.collision R hR (JetTransport.map R t g))) := by
  rw [JetKineticField.field,map_smul,spatialDerivative_transport]

/-- An exact energy derivative, with the actual full nonlinear collision source.
The only time equation assumed here is the original proved Picard integral
in its true compatible moving frame. -/
theorem moving_frame_energy_derivative {R T : ℝ} (hR : 0 ≤ R) (hT : 0 ≤ T)
    (c : ℝ) (p₀ : Space R) (g : ℝ → Space R) (hg : ContinuousOn g (Icc 0 T))
    (he : ∀ t ∈ Icc 0 T,g t=p₀+∫ s in (0 : ℝ)..t,JetKineticField.field R hR c s (g s))
    (n : ℕ) (hn : n ≤ 3) (v : Fin n → RealPosition)
    {w : ℝ → Distribution R} {w' : Distribution R} {t : ℝ} (ht : t ∈ Icc 0 T)
    (hw : HasDerivWithinAt w w' (Icc 0 T) t) :
    HasDerivWithinAt (fun τ => derivativeEnergy R n hn v (w τ) (g τ))
      ((1/2:ℝ)*integralCLM R (w'*(spatialDerivative R n hn v (g t)*
        spatialDerivative R n hn v (g t)))+
       integralCLM R (w t*(spatialDerivative R n hn v (g t)*
        (c • transport R (-t) (spatialDerivative R n hn v
          (JetCollision.collision R hR (JetTransport.map R t (g t)))))))) (Icc 0 T) t := by
  have hd := (spatialDerivative R n hn v).hasFDerivAt.comp_hasDerivWithinAt t
    (JetMildEquation.moving_frame_hasDerivWithinAt hR hT c p₀ g hg he t ht)
  have h := quadratic_hasDerivWithinAt R hw hd
  rw [field_spatialDerivative] at h
  exact h

def collisionPairing (R : ℝ) (hR : 0 ≤ R) (n : ℕ) (hn : n ≤ 3)
    (v : Fin n → RealPosition) (w : Distribution R) (p : Space R) : ℝ :=
  integralCLM R (w*(spatialDerivative R n hn v p *
    spatialDerivative R n hn v (JetCollision.collision R hR p)))

theorem collision_pairing_physical (R : ℝ) (hR : 0 ≤ R) (c t : ℝ)
    (n : ℕ) (hn : n ≤ 3) (v : Fin n → RealPosition) (w : Distribution R)
    (g : Space R) :
    integralCLM R (transport R (-t) w*(spatialDerivative R n hn v g *
      (c • transport R (-t) (spatialDerivative R n hn v
        (JetCollision.collision R hR (JetTransport.map R t g)))))) =
      c*collisionPairing R hR n hn v w (JetTransport.map R t g) := by
  rw [mul_smul_comm,mul_smul_comm,map_smul]
  simp only [smul_eq_mul]
  rw [triple_moving_to_physical]
  unfold collisionPairing
  rw [spatialDerivative_transport]

/-- The exact physical-coordinate energy identity. The weight hypothesis is
its actual material derivative, expressed in the same characteristic frame;
it is not a bound or a substitute evolution. -/
theorem physical_energy_derivative {R T : ℝ} (hR : 0 ≤ R) (hT : 0 ≤ T)
    (c : ℝ) (p₀ : Space R) (g : ℝ → Space R) (hg : ContinuousOn g (Icc 0 T))
    (he : ∀ t ∈ Icc 0 T,g t=p₀+∫ s in (0 : ℝ)..t,JetKineticField.field R hR c s (g s))
    (n : ℕ) (hn : n ≤ 3) (v : Fin n → RealPosition)
    {w : ℝ → Distribution R} {b : Distribution R} {t : ℝ} (ht : t ∈ Icc 0 T)
    (hw : HasDerivWithinAt (fun τ => transport R (-τ) (w τ))
      (transport R (-t) b) (Icc 0 T) t) :
    HasDerivWithinAt
      (fun τ => derivativeEnergy R n hn v (w τ) (JetTransport.map R τ (g τ)))
      (derivativeEnergy R n hn v b (JetTransport.map R t (g t)) +
        c*collisionPairing R hR n hn v (w t) (JetTransport.map R t (g t))) (Icc 0 T) t := by
  have h := moving_frame_energy_derivative hR hT c p₀ g hg he n hn v ht hw
  rw [collision_pairing_physical] at h
  change HasDerivWithinAt _
    (quadratic R (transport R (-t) b) (spatialDerivative R n hn v (g t)) + _) _ _ at h
  rw [quadratic_moving_to_physical,←spatialDerivative_transport] at h
  apply h.congr_of_mem _ ht
  intro τ _
  unfold derivativeEnergy
  rw [quadratic_moving_to_physical,spatialDerivative_transport]

abbrev SpatialIndex := (n : Fin 4) × (Fin n.val → Fin 3)

def coordinateDirections (a : SpatialIndex) : Fin a.1.val → RealPosition :=
  fun i => Pi.single (a.2 i) 1

def h3Energy (R : ℝ) (w : Distribution R) (p : Space R) : ℝ :=
  ∑ a : SpatialIndex,derivativeEnergy R a.1.val (by omega) (coordinateDirections a) w p

def h3CollisionPairing (R : ℝ) (hR : 0 ≤ R) (w : Distribution R) (p : Space R) : ℝ :=
  ∑ a : SpatialIndex,collisionPairing R hR a.1.val (by omega) (coordinateDirections a) w p

/-- The complete 0--3 spatial energy, with all ordered coordinate derivatives.
It is one energy of one solution, not a set of unrelated jet equations. -/
theorem physical_h3_energy_derivative {R T : ℝ} (hR : 0 ≤ R) (hT : 0 ≤ T)
    (c : ℝ) (p₀ : Space R) (g : ℝ → Space R) (hg : ContinuousOn g (Icc 0 T))
    (he : ∀ t ∈ Icc 0 T,g t=p₀+∫ s in (0 : ℝ)..t,JetKineticField.field R hR c s (g s))
    {w : ℝ → Distribution R} {b : Distribution R} {t : ℝ} (ht : t ∈ Icc 0 T)
    (hw : HasDerivWithinAt (fun τ => transport R (-τ) (w τ))
      (transport R (-t) b) (Icc 0 T) t) :
    HasDerivWithinAt (fun τ => h3Energy R (w τ) (JetTransport.map R τ (g τ)))
      (h3Energy R b (JetTransport.map R t (g t))+
        c*h3CollisionPairing R hR (w t) (JetTransport.map R t (g t))) (Icc 0 T) t := by
  have h := HasDerivWithinAt.sum (u := Finset.univ)
    (fun a _ => physical_energy_derivative hR hT c p₀ g hg he
      a.1.val (by omega) (coordinateDirections a) ht hw)
  simpa only [h3Energy,h3CollisionPairing,Finset.sum_add_distrib,Finset.mul_sum] using h

end
end Resonance.JetEnergy

#check Resonance.JetEnergy.spatialDerivative_actual
#print axioms Resonance.JetEnergy.spatialDerivative_actual
#check Resonance.JetEnergy.spatialDerivative_transport
#print axioms Resonance.JetEnergy.spatialDerivative_transport
#check Resonance.JetEnergy.derivativeEnergy_transport
#print axioms Resonance.JetEnergy.derivativeEnergy_transport
#check Resonance.JetEnergy.field_spatialDerivative
#print axioms Resonance.JetEnergy.field_spatialDerivative
#check Resonance.JetEnergy.moving_frame_energy_derivative
#print axioms Resonance.JetEnergy.moving_frame_energy_derivative
#check Resonance.JetEnergy.collision_pairing_physical
#print axioms Resonance.JetEnergy.collision_pairing_physical
#check Resonance.JetEnergy.physical_energy_derivative
#print axioms Resonance.JetEnergy.physical_energy_derivative
#check Resonance.JetEnergy.physical_h3_energy_derivative
#print axioms Resonance.JetEnergy.physical_h3_energy_derivative
