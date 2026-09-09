import Resonance.NormalizedCubicRemainder
import Resonance.ContinuousSourceCoordinates

/-! The actual quadratic/cubic remainder satisfies the original five
unweighted moment constraints. The compatibility supplied to the strong
resolvent is derived from the full collision, not assumed. -/
open Set MeasureTheory
open scoped ENNReal BigOperators
namespace Resonance.NormalizedRemainderMoments
noncomputable section
set_option maxHeartbeats 2000000
open ResonantMeasure Thermodynamics ProfileBanachSmooth NormalizedCubicOneY
open NormalizedCubicRemainder ContinuousCollisionMoments
open CubeLinftyCoordinates ActualPairNormalization PhysicalFiveBasis PhysicalMomentProjection
open ContinuousSourceCoordinates

theorem collision_derivative_moments {R : ℝ} (hR : 0≤R) (a : Parameter) (f h : X R) :
    ContinuousCollisionMoments.moment R a
      (fderiv ℝ (FiberContinuity.collisionMap R hR) f h)=0 := by
  have hd := (CollisionMultilinear.collisionMap_hasFDerivAt hR f).differentiableAt.hasFDerivAt
  have hc := (ContinuousCollisionMoments.moment R a).hasFDerivAt.comp f hd
  have he : (fun g : X R=>ContinuousCollisionMoments.moment R a (FiberContinuity.collisionMap R hR g))=
      (fun _ : X R=>(0:ℝ)) := funext (fun g=>collision_five_moments hR g a)
  change HasFDerivAt (fun g : X R=>ContinuousCollisionMoments.moment R a (FiberContinuity.collisionMap R hR g))
    ((ContinuousCollisionMoments.moment R a).comp (fderiv ℝ (FiberContinuity.collisionMap R hR) f)) f at hc
  rw [he] at hc
  have hz := hc.unique (hasFDerivAt_const (0:ℝ) f)
  have hh := congrArg (fun T : X R→L[ℝ]ℝ=>T h) hz
  simpa only [ContinuousLinearMap.comp_apply,ContinuousLinearMap.zero_apply] using hh

theorem profile_times_denominator {R : ℝ} {θ : Parameter} (hθ : θ∈positiveDomain R) :
    profileMap R θ*denominatorMap R θ=1 := by
  rw [profileMap_eq hθ]
  exact (denominatorUnit hθ).inv_val

theorem actual_physical_remainder {R : ℝ} (hR : 0≤R) {θ : Parameter}
    (hθ : θ∈positiveDomain R) (q : X R) :
    profileMap R θ*remainder R hR θ q=
      FiberContinuity.collisionMap R hR (profileMap R θ*(1+q))-
        fderiv ℝ (FiberContinuity.collisionMap R hR) (profileMap R θ) (profileMap R θ*q) := by
  have he := congrArg (fun f : X R=>profileMap R θ*f) (actual_normalized_decomposition hR hθ q)
  simp only [mul_add,←mul_assoc,profile_times_denominator hθ,one_mul] at he
  apply eq_sub_iff_add_eq.mpr
  rw [add_comm]
  simpa only [mul_add] using he.symm

theorem actual_remainder_five_moments {R : ℝ} (hR : 0≤R) {θ : Parameter}
    (hθ : θ∈positiveDomain R) (q : X R) (a : Parameter) :
    ContinuousCollisionMoments.moment R a (profileMap R θ*remainder R hR θ q)=0 := by
  rw [actual_physical_remainder hR hθ,map_sub,collision_five_moments,
    collision_derivative_moments,sub_self]

theorem actual_remainder_source_micro {R : ℝ} (hR : 0<R) {θ : Parameter}
    (hθ : θ∈positiveDomain R) (q : X R) :
    projection hR hθ (StrongBoundedCell.sourceVector hR (embed R (remainder R hR.le θ q)))=0 := by
  have ha : analysisMap hR hθ (StrongBoundedCell.sourceVector hR (embed R (remainder R hR.le θ q)))=0 := by
    ext i
    change analysisMap hR hθ (ContinuousSourceCoordinates.sourceMap hR (remainder R hR.le θ q)) i=0
    rw [analysis_source_embed hR hθ]
    exact actual_remainder_five_moments hR.le hθ q (Pi.single i 1)
  change synthesis hR.le hθ (gramInverse hR hθ (analysisMap hR hθ _))=0
  rw [ha,map_zero,map_zero]

end
end Resonance.NormalizedRemainderMoments
