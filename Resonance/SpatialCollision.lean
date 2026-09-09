import Resonance.FiberContinuity
import Resonance.TransportDuhamel

/-! The original full four-wave collision operator on the same spatial torus
and closed momentum cube as the physical free-transport group. The spatial
lift keeps one common input distribution in all four collision legs. -/
open Set Metric

namespace Resonance.SpatialCollision
noncomputable section
open ResonantMeasure FreeTransport CollisionFiber

def momentumSection {R : ℝ} (f : Distribution R) (x : SpatialTorus) :
    C(MomentumDomain R, ℝ) := f.curry x

theorem momentumSection_apply {R : ℝ} (f : Distribution R) (x : SpatialTorus)
    (k : MomentumDomain R) : momentumSection f x k = f (x,k) := rfl

theorem momentumSection_norm_le {R : ℝ} (f : Distribution R) (x : SpatialTorus) :
    ‖momentumSection f x‖ ≤ ‖f‖ :=
  (ContinuousMap.norm_le _ (norm_nonneg f)).mpr (fun k => f.norm_coe_le_norm (x,k))

theorem momentumSection_sub {R : ℝ} (f g : Distribution R) (x : SpatialTorus) :
    momentumSection (f-g) x = momentumSection f x - momentumSection g x := by
  ext k
  rfl

/-- The nonlinear operator acts on each actual spatial fiber of one distribution. -/
def collision (R : ℝ) (hR : 0 ≤ R) (f : Distribution R) : Distribution R :=
  ContinuousMap.uncurry
    ⟨fun x => FiberContinuity.collisionMap R hR (momentumSection f x),
      (FiberContinuity.collisionMap_continuous hR).comp f.curry.continuous⟩

theorem collision_apply (R : ℝ) (hR : 0 ≤ R) (f : Distribution R)
    (x : SpatialTorus) (k : MomentumDomain R) :
    collision R hR f (x,k) = FiberContinuity.collisionMap R hR (momentumSection f x) k := rfl

theorem collision_apply_original (R : ℝ) (hR : 0 ≤ R) (f : Distribution R)
    (x : SpatialTorus) (k : MomentumDomain R) (g : E → ℝ)
    (hg : ∀ p : MomentumDomain R, g p = f (x,p)) :
    collision R hR f (x,k) = collisionOutput R g k :=
  FiberContinuity.collisionMap_apply R hR (momentumSection f x) g hg k

theorem collision_norm_le (R : ℝ) (hR : 0 ≤ R) (f : Distribution R) :
    ‖collision R hR f‖ ≤ 4 * ‖f‖^3 * (fiberMassBound R).toReal := by
  apply (ContinuousMap.norm_le _ (by positivity)).mpr
  intro p
  calc
    _ ≤ ‖FiberContinuity.collisionMap R hR (momentumSection f p.1)‖ :=
      (FiberContinuity.collisionMap R hR (momentumSection f p.1)).norm_coe_le_norm p.2
    _ ≤ 4 * ‖momentumSection f p.1‖^3 * (fiberMassBound R).toReal :=
      FiberContinuity.collisionMap_norm_le R hR _
    _ ≤ _ := by gcongr; exact momentumSection_norm_le f p.1

theorem collision_sub_norm_le {R M : ℝ} (hR : 0 ≤ R) (hM : 0 ≤ M)
    (f g : Distribution R) (hf : ‖f‖ ≤ M) (hg : ‖g‖ ≤ M) :
    ‖collision R hR f - collision R hR g‖ ≤
      (12 * M^2 * (fiberMassBound R).toReal) * ‖f-g‖ := by
  apply (ContinuousMap.norm_le _ (by positivity)).mpr
  intro p
  calc
    _ ≤ ‖FiberContinuity.collisionMap R hR (momentumSection f p.1) -
        FiberContinuity.collisionMap R hR (momentumSection g p.1)‖ :=
      (FiberContinuity.collisionMap R hR (momentumSection f p.1) -
        FiberContinuity.collisionMap R hR (momentumSection g p.1)).norm_coe_le_norm p.2
    _ ≤ (12 * M^2 * (fiberMassBound R).toReal) *
        ‖momentumSection f p.1 - momentumSection g p.1‖ :=
      FiberContinuity.collisionMap_sub_norm_le hR hM _ _
        ((momentumSection_norm_le f p.1).trans hf) ((momentumSection_norm_le g p.1).trans hg)
    _ ≤ _ := by
      rw [← momentumSection_sub]
      exact mul_le_mul_of_nonneg_left (momentumSection_norm_le (f-g) p.1) (by positivity)

theorem collision_lipschitzOnWith {R M : ℝ} (hR : 0 ≤ R) (hM : 0 ≤ M) :
    LipschitzOnWith ⟨12 * M^2 * (fiberMassBound R).toReal, by positivity⟩
      (collision R hR) (closedBall 0 M) := by
  apply lipschitzOnWith_iff_dist_le_mul.mpr
  intro f hf g hg
  have hf' : ‖f‖ ≤ M := by simpa [mem_closedBall, dist_zero_right] using hf
  have hg' : ‖g‖ ≤ M := by simpa [mem_closedBall, dist_zero_right] using hg
  simpa only [dist_eq_norm, NNReal.coe_mk] using collision_sub_norm_le hR hM f g hf' hg'

theorem collision_continuous {R : ℝ} (hR : 0 ≤ R) : Continuous (collision R hR) := by
  apply continuous_iff_continuousAt.mpr
  intro f
  apply (collision_lipschitzOnWith hR (M := ‖f‖+1) (by positivity)).continuousOn.continuousAt
  apply Metric.closedBall_mem_nhds_of_mem
  simp [mem_ball, dist_zero_right]

theorem collision_zero {R : ℝ} (hR : 0 ≤ R) : collision R hR 0 = 0 := by
  apply norm_eq_zero.mp
  exact le_antisymm (by simpa using collision_norm_le R hR 0) (norm_nonneg _)

end
end Resonance.SpatialCollision
