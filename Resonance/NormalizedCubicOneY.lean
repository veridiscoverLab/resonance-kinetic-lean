import Resonance.OneWeightedCollision

/-! The normalized full cubic is constructed from the original collision
trilinear map and the actual Rayleigh--Jeans profile. Its one-Y bounds
retain all four parents and all three input positions. -/
open Set
open scoped BigOperators ContDiff
namespace Resonance.NormalizedCubicOneY
noncomputable section
set_option maxHeartbeats 1800000
open ResonantMeasure Thermodynamics ProfileBanachSmooth
open CollisionMultilinear OneWeightedParent OneWeightedPairReadout OneWeightedCollision

abbrev X (R : ℝ) := C(cube R,ℝ)

def normalizedTrilinear (R : ℝ) (hR : 0≤R) (θ : Parameter) :
    ContinuousMultilinearMap ℝ (fun _ : Fin 3=>X R) (X R) :=
  (ContinuousLinearMap.mul ℝ (X R) (denominatorMap R θ)).compContinuousMultilinearMap
    ((collisionTrilinear R hR).compContinuousLinearMap
      (fun _=>ContinuousLinearMap.mul ℝ (X R) (profileMap R θ)))

theorem normalizedTrilinear_apply (R : ℝ) (hR : 0≤R) (θ : Parameter) (m : Fin 3→X R) :
    normalizedTrilinear R hR θ m=denominatorMap R θ*
      collisionTrilinear R hR (fun i=>profileMap R θ*m i) := rfl

theorem normalizedTrilinear_diagonal (R : ℝ) (hR : 0≤R) (θ : Parameter) (f : X R) :
    normalizedTrilinear R hR θ (fun _=>f)=
      denominatorMap R θ*FiberContinuity.collisionMap R hR (profileMap R θ*f) := by
  rw [normalizedTrilinear_apply,collisionTrilinear_diagonal]

def oneYBound {R : ℝ} (hR : 0<R) (θ : Parameter) : ℝ :=
  1+4*oneYConstant hR*‖denominatorMap R θ‖*‖profileMap R θ‖^3

theorem oneYBound_positive {R : ℝ} (hR : 0<R) (θ : Parameter) : 0<oneYBound hR θ := by
  have h := (oneYConstant_positive hR).le
  unfold oneYBound
  positivity

theorem weighted_mul_bound {R : ℝ} (hR : 0≤R) (N u : X R) :
    ‖referenceContinuous hR*(N*u)‖≤‖N‖*‖referenceContinuous hR*u‖ := by
  rw [mul_left_comm (referenceContinuous hR) N u]
  exact norm_mul_le _ _

theorem normalized_oneY_from_slot {R : ℝ} (hR : 0<R) (θ : Parameter) (n a b : Fin 3)
    (hb : ∀m : Fin 3→X R,‖collisionTrilinear R hR.le m‖≤
      4*oneYConstant hR*‖referenceContinuous hR.le*m n‖*‖m a‖*‖m b‖)
    (m : Fin 3→X R) :
    ‖normalizedTrilinear R hR.le θ m‖≤oneYBound hR θ*
      ‖referenceContinuous hR.le*m n‖*‖m a‖*‖m b‖ := by
  have hC := (oneYConstant_positive hR).le
  have hnorm := norm_nonneg (profileMap R θ)
  rw [normalizedTrilinear_apply]
  calc
    _ ≤ ‖denominatorMap R θ‖*‖collisionTrilinear R hR.le (fun i=>profileMap R θ*m i)‖ := norm_mul_le _ _
    _ ≤ ‖denominatorMap R θ‖*(4*oneYConstant hR*
        ‖referenceContinuous hR.le*(profileMap R θ*m n)‖*‖profileMap R θ*m a‖*‖profileMap R θ*m b‖) :=
      mul_le_mul_of_nonneg_left (hb _) (norm_nonneg _)
    _ ≤ ‖denominatorMap R θ‖*(4*oneYConstant hR*
        (‖profileMap R θ‖*‖referenceContinuous hR.le*m n‖)*
        (‖profileMap R θ‖*‖m a‖)*(‖profileMap R θ‖*‖m b‖)) := by
      gcongr
      · exact weighted_mul_bound hR.le _ _
      · exact norm_mul_le _ _
      · exact norm_mul_le _ _
    _ = (4*oneYConstant hR*‖denominatorMap R θ‖*‖profileMap R θ‖^3)*
        ‖referenceContinuous hR.le*m n‖*‖m a‖*‖m b‖ := by ring
    _ ≤ _ := by
      gcongr
      exact le_add_of_nonneg_left (by norm_num)

theorem normalized_first_oneY {R : ℝ} (hR : 0<R) (θ : Parameter) (m : Fin 3→X R) :
    ‖normalizedTrilinear R hR.le θ m‖≤oneYBound hR θ*
      ‖referenceContinuous hR.le*m 0‖*‖m 1‖*‖m 2‖ :=
  normalized_oneY_from_slot hR θ 0 1 2 (collision_first_oneY hR) m

theorem normalized_second_oneY {R : ℝ} (hR : 0<R) (θ : Parameter) (m : Fin 3→X R) :
    ‖normalizedTrilinear R hR.le θ m‖≤oneYBound hR θ*
      ‖referenceContinuous hR.le*m 1‖*‖m 0‖*‖m 2‖ :=
  normalized_oneY_from_slot hR θ 1 0 2 (collision_second_oneY hR) m

theorem normalized_third_oneY {R : ℝ} (hR : 0<R) (θ : Parameter) (m : Fin 3→X R) :
    ‖normalizedTrilinear R hR.le θ m‖≤oneYBound hR θ*
      ‖referenceContinuous hR.le*m 2‖*‖m 0‖*‖m 1‖ :=
  normalized_oneY_from_slot hR θ 2 0 1 (collision_third_oneY hR) m

theorem actual_normalized_diagonal {R : ℝ} (hR : 0≤R) {θ : Parameter}
    (_hθ : θ∈positiveDomain R) (f : X R) (k : cube R) :
    normalizedTrilinear R hR θ (fun _=>f) k=
      FiberContinuity.collisionMap R hR (profileMap R θ*f) k/WeightedJointMeasure.profile θ k := by
  rw [normalizedTrilinear_diagonal]
  change denominatorMap R θ k*_=_
  rw [denominatorMap_apply,profile_eq_inverse_denominator,div_inv_eq_mul,mul_comm]

end
end Resonance.NormalizedCubicOneY
