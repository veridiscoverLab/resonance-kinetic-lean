import Resonance.ContinuousCollisionEntropy
import Resonance.PhaseLogEntropy

/-! The logarithmic entropy balance of the actual positive mild
solution, on the original full phase measure and original quartet measure. -/
open Set MeasureTheory
namespace Resonance.PhaseCollisionEntropy
noncomputable section
open FreeTransport PhaseEnergy PhaseLogEntropy ContinuousLogPath
open ContinuousCollisionMoments ContinuousCollisionEntropy JetCollision

def phaseProduction (R : ℝ) (f : Distribution R) : ℝ :=
  ∫ X : SpatialTorus,cubeProduction R (f.curry X)

theorem phase_collision_production {R : ℝ} (hR : 0≤R)
    (f : Distribution R) (hf : ∀ z,0 < f z) :
    integralCLM R (SpatialCollision.collision R hR f*Ring.inverse f)=phaseProduction R f := by
  change (∫ z,(SpatialCollision.collision R hR f*Ring.inverse f) z
    ∂((volume : Measure SpatialTorus).prod (momentumMeasure R)))=_
  rw [integral_prod _ (continuous_integrable R (SpatialCollision.collision R hR f*Ring.inverse f))]
  apply integral_congr_ae
  apply ae_of_all
  intro X
  dsimp only
  rw [←actual_collision_entropy hR (f.curry X) (fun k=>hf (X,k))]
  change (∫ k,SpatialCollision.collision R hR f (X,k)*Ring.inverse f (X,k) ∂momentumMeasure R)=
    ∫ k,FiberContinuity.collisionMap R hR (f.curry X) k*Ring.inverse (f.curry X) k ∂momentumMeasure R
  apply integral_congr_ae
  apply ae_of_all
  intro k
  dsimp only
  rw [ring_inverse_apply f (fun z=>(hf z).ne'),
    ring_inverse_apply (f.curry X) (fun k=>(hf (X,k)).ne')]
  rfl

theorem phaseProduction_nonnegative {R : ℝ} (f : Distribution R) (hf : ∀ z,0 < f z) :
    0 ≤ phaseProduction R f := integral_nonneg (fun X=>cubeProduction_nonnegative _ (fun k=>hf (X,k)))

theorem original_mild_entropy_balance {R T : ℝ} (hR : 0≤R) (hT : 0≤T)
    (c : ℝ) (p₀ : Space R) (p : ℝ→Space R) (hp : ContinuousOn p (Icc 0 T))
    (he : ∀ t∈Icc 0 T,readback (p t)=transport R t (readback p₀)+
      ∫ s in (0 : ℝ)..t,c • transport R (t-s)
        (SpatialCollision.collision R hR (readback (p s))))
    (hpos : ∀ t∈Icc 0 T,∀ z,0 < readback (p t) z) {t : ℝ} (ht : t∈Icc 0 T) :
    HasDerivWithinAt (fun τ=>entropy R (readback (p τ)))
      (-c*phaseProduction R (readback (p t))) (Icc 0 T) t := by
  have h := original_mild_entropy_derivative hR hT c p₀ p hp he
    (fun τ hτ z=>(hpos τ hτ z).ne') ht
  rwa [phase_collision_production hR _ (hpos t ht)] at h

end
end Resonance.PhaseCollisionEntropy
