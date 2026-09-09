import Resonance.ContinuousCollisionForm
import Resonance.NonlinearEntropy
import Resonance.ContinuousLogPath

/-! The actual continuous collision output paired with its reciprocal
is exactly the original complete four-leg logarithmic production. -/
open Set MeasureTheory
open scoped ENNReal
namespace Resonance.ContinuousCollisionEntropy
noncomputable section
open ResonantMeasure FreeTransport FiberContinuity CollisionFiber
open ContinuousCollisionMoments PhaseEnergy ContinuousCollisionForm
open ContinuousLogPath NonlinearEntropy WeakCollision
local notation "CubeFunction" => ContinuousCollisionMoments.CubeFunction

def cubeProduction (R : ℝ) (f : CubeFunction R) : ℝ :=
  production R (continuousExtension R f)

theorem positive_extension {R : ℝ} (f : CubeFunction R) (hf : ∀ k,0 < f k) :
    ∀ᵐ k ∂PhysicalMarginal.physicalMeasure R,0 < continuousExtension R f k := by
  filter_upwards [ae_restrict_mem (measurable_cube R)] with k hk
  rw [continuousExtension_eq R f ⟨k,hk⟩]
  exact hf ⟨k,hk⟩

theorem inverse_extension {R : ℝ} (f : CubeFunction R) (hf : ∀ k,f k≠0) :
    (continuousExtension R (Ring.inverse f) : E→ℝ) =ᵐ[PhysicalMarginal.physicalMeasure R]
      (fun k=>(continuousExtension R f k)⁻¹) := by
  filter_upwards [ae_restrict_mem (measurable_cube R)] with k hk
  rw [continuousExtension_eq R _ ⟨k,hk⟩,continuousExtension_eq R f ⟨k,hk⟩,ring_inverse_apply f hf]

theorem actual_collision_entropy {R : ℝ} (hR : 0≤R)
    (f : CubeFunction R) (hf : ∀ k,0 < f k) :
    cubeIntegral R (collisionMap R hR f*Ring.inverse f)=cubeProduction R f := by
  let F := continuousExtension R f
  let G := continuousExtension R (Ring.inverse f)
  have hG := inverse_extension f (fun k=>(hf k).ne')
  have hw := collision_weak_pairing hR F G
  rw [restrictCube_extension,restrictCube_extension] at hw
  rw [mul_comm,hw]
  change (∫ k,density F G k ∂pairingMeasure R) =
    ∫ k,productionDensity F k ∂pairingMeasure R
  have ha : ∀ᵐ k ∂pairingMeasure R,∀ i : Fin 4,G (k i)=(F (k i))⁻¹ := by
    rw [ae_all_iff]
    intro i
    exact (JointMultiplier.leg_quasiMeasurePreserving_cube R i).ae hG
  apply integral_congr_ae
  filter_upwards [ha,productionDensity_eq_density_ae (positive_extension f hf)] with k hk hp
  rw [hp]
  unfold density
  congr 1
  funext i
  exact hk i

theorem cubeProduction_nonnegative {R : ℝ} (f : CubeFunction R) (hf : ∀ k,0 < f k) :
    0 ≤ cubeProduction R f := production_nonneg (positive_extension f hf)

theorem cubeProduction_integrable_quartet {R : ℝ} (hR : 0≤R)
    (f : CubeFunction R) (hf : ∀ k,0 < f k) :
    Integrable (productionDensity (continuousExtension R f)) (pairingMeasure R) := by
  have hi : MemLp (fun k=>(continuousExtension R f k)⁻¹) ∞ (PhysicalMarginal.physicalMeasure R) :=
    (memLp_congr_ae (inverse_extension f (fun k=>(hf k).ne'))).mp (extension_memLp R (Ring.inverse f))
  exact productionDensity_integrable hR (extension_memLp R f) hi (positive_extension f hf)

end
end Resonance.ContinuousCollisionEntropy
