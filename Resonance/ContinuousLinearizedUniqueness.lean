import Resonance.ContinuousResolventBounds

/-! Uniqueness for the original continuous linearized regularized
equation, directly from the full nonnegative physical collision form. -/
open Set MeasureTheory
namespace Resonance.ContinuousLinearizedUniqueness
noncomputable section
set_option maxHeartbeats 1800000
open ResonantMeasure Thermodynamics ProfileBanachSmooth ContinuousSourceCoordinates
open ContinuousSourceForm ContinuousCollisionMoments PhysicalWeightedCoercivity
open ContinuousRegularizedEquation PhysicalMomentProjection

def linearAction {R : ℝ} (hR : 0≤R) (θ : Parameter) : C(cube R,ℝ)→L[ℝ]C(cube R,ℝ) :=
  (ContinuousLinearMap.mul ℝ C(cube R,ℝ) (denominatorMap R θ)).comp
    ((fderiv ℝ (FiberContinuity.collisionMap R hR) (profileMap R θ)).comp
      (ContinuousLinearMap.mul ℝ C(cube R,ℝ) (profileMap R θ)))

theorem linearAction_apply {R : ℝ} (hR : 0≤R) (θ : Parameter) (q : C(cube R,ℝ)) :
    linearAction hR θ q=denominatorMap R θ*
      fderiv ℝ (FiberContinuity.collisionMap R hR) (profileMap R θ) (profileMap R θ*q) := rfl

theorem linearAction_pairing {R : ℝ} (hR : 0<R) {θ : Parameter}
    (hθ : θ∈positiveDomain R) (u v : C(cube R,ℝ)) :
    cubeIntegral R (v*linearAction hR.le θ u)=
      -physicalForm hR.le hθ (sourceMap hR u) (sourceMap hR v) :=
  normalized_derivative_pairing hR hθ u v

theorem homogeneous_zero {R : ℝ} (hR : 0<R) {θ : Parameter}
    (hθ : θ∈positiveDomain R) {s : ℝ} (hs : 0 ≤ s) (q : C(cube R,ℝ))
    (he : q-s • linearAction hR.le θ q=0) : q=0 := by
  have hi := congrArg (fun f : C(cube R,ℝ)=>cubeIntegral R (q*f)) he
  change cubeIntegral R (q*(q-s • linearAction hR.le θ q))=cubeIntegral R (q*0) at hi
  have hmul : q*(q-s • linearAction hR.le θ q)=q*q-s • (q*linearAction hR.le θ q) := by
    rw [mul_sub,mul_smul_comm]
  rw [hmul,map_sub,map_smul,mul_zero,map_zero,linearAction_pairing hR hθ] at hi
  simp only [smul_eq_mul] at hi
  have hpos : 0≤physicalForm hR.le hθ (sourceMap hR q) (sourceMap hR q) := by
    rw [physical_form_square]
    positivity
  have hsq : 0≤cubeIntegral R (q*q) := by
    exact integral_nonneg (fun k=>mul_self_nonneg (q k))
  apply cube_square_zero hR q
  nlinarith

theorem actual_continuous_linearized_unique {R : ℝ} (hR : 0<R) {θ : Parameter}
    (hθ : θ∈positiveDomain R) {s : ℝ} (hs : 0 ≤ s) (q r : C(cube R,ℝ))
    (he : q-s • linearAction hR.le θ q=r-s • linearAction hR.le θ r) : q=r := by
  apply sub_eq_zero.mp
  apply homogeneous_zero hR hθ hs (q-r)
  rw [map_sub,smul_sub]
  have hzero := sub_eq_zero.mpr he
  convert hzero using 1
  abel

theorem original_solution_eq_output {R : ℝ} (hR : 0<R) {θ : Parameter}
    (hθ : θ∈positiveDomain R) {s : ℝ} (hs : 0<s) (q F : C(cube R,ℝ))
    (hF : projection hR hθ (sourceMap hR F)=0)
    (he : q-s • linearAction hR.le θ q=F) : q=output hR hθ hs F := by
  apply actual_continuous_linearized_unique hR hθ hs.le
  rw [he]
  exact (actual_continuous_regularized_equation hR hθ hs F hF).symm

end
end Resonance.ContinuousLinearizedUniqueness
