import Resonance.NormalizedCubicOneY
import Mathlib.Analysis.Normed.Module.Multilinear.Curry

/-! Four actual RJ coefficient slots of the complete cubic collision.
The fixed physical inputs are not separated into different quartets.
The operator norm of this coefficient map retains one ν_* input. -/
open scoped BigOperators
namespace Resonance.CubicParameterCoefficients
noncomputable section
set_option maxHeartbeats 2400000
open ResonantMeasure CollisionMultilinear ProfileBanachSmooth NormalizedCubicOneY
open OneWeightedPairReadout OneWeightedParent OneWeightedCollision

abbrev Coeff (R : ℝ) := ContinuousMultilinearMap ℝ (fun _ : Fin 4=>X R) (X R)
abbrev Triple (R : ℝ) := ContinuousMultilinearMap ℝ (fun _ : Fin 3=>X R) (X R)

def innerCoefficients (R : ℝ) (hR : 0≤R) (u : Fin 3→X R) : Triple R :=
  (collisionTrilinear R hR).compContinuousLinearMap
    (fun i=>ContinuousLinearMap.mul ℝ (X R) (u i))

def leftCoefficients (R : ℝ) (hR : 0≤R) (u : Fin 3→X R) : X R→L[ℝ]Triple R :=
  MultilinearMap.mkContinuousLinear
    { toFun D := (ContinuousLinearMap.mul ℝ (X R) D).toLinearMap.compMultilinearMap
        (innerCoefficients R hR u).toMultilinearMap
      map_add' D E := by apply MultilinearMap.ext; intro m; exact add_mul D E _
      map_smul' a D := by apply MultilinearMap.ext; intro m; exact smul_mul_assoc a D _ }
    ‖innerCoefficients R hR u‖ (fun D m=>by
      change ‖D*innerCoefficients R hR u m‖≤_
      exact (norm_mul_le _ _).trans ((mul_le_mul_of_nonneg_left
        ((innerCoefficients R hR u).le_opNorm m) (norm_nonneg D)).trans_eq (by ring)))

def coefficientMap (R : ℝ) (hR : 0≤R) (u : Fin 3→X R) : Coeff R :=
  (leftCoefficients R hR u).uncurryLeft

theorem coefficientMap_apply (R : ℝ) (hR : 0≤R) (u : Fin 3→X R) (m : Fin 4→X R) :
    coefficientMap R hR u m=m 0*collisionTrilinear R hR (fun i=>u i*m i.succ) := rfl

theorem coefficientMap_normalized (R : ℝ) (hR : 0≤R) (θ : Thermodynamics.Parameter)
    (u : Fin 3→X R) :
    coefficientMap R hR u ![denominatorMap R θ,profileMap R θ,profileMap R θ,profileMap R θ]=
      normalizedTrilinear R hR θ u := by
  rw [coefficientMap_apply,normalizedTrilinear_apply]
  congr 1
  apply congrArg (collisionTrilinear R hR)
  funext i
  fin_cases i <;> exact mul_comm _ _

theorem coefficientMap_norm_from_slot {R : ℝ} (hR : 0<R) (n a b : Fin 3)
    (hp : ∀v : Fin 3→ℝ,v n*v a*v b=v 0*v 1*v 2)
    (hb : ∀v : Fin 3→X R,‖collisionTrilinear R hR.le v‖≤
      4*oneYConstant hR*‖referenceContinuous hR.le*v n‖*‖v a‖*‖v b‖)
    (u : Fin 3→X R) :
    ‖coefficientMap R hR.le u‖≤4*oneYConstant hR*
      ‖referenceContinuous hR.le*u n‖*‖u a‖*‖u b‖ := by
  have hC := (oneYConstant_positive hR).le
  apply ContinuousMultilinearMap.opNorm_le_bound (by positivity)
  intro m
  rw [coefficientMap_apply]
  calc
    _ ≤ ‖m 0‖*‖collisionTrilinear R hR.le (fun i=>u i*m i.succ)‖ := norm_mul_le _ _
    _ ≤ ‖m 0‖*(4*oneYConstant hR*‖referenceContinuous hR.le*(u n*m n.succ)‖*
        ‖u a*m a.succ‖*‖u b*m b.succ‖) := mul_le_mul_of_nonneg_left (hb _) (norm_nonneg _)
    _ ≤ ‖m 0‖*(4*oneYConstant hR*(‖m n.succ‖*‖referenceContinuous hR.le*u n‖)*
        (‖u a‖*‖m a.succ‖)*(‖u b‖*‖m b.succ‖)) := by
      gcongr
      · rw [mul_comm (u n)]
        exact weighted_mul_bound hR.le _ _
      · exact norm_mul_le _ _
      · exact norm_mul_le _ _
    _ = (4*oneYConstant hR*‖referenceContinuous hR.le*u n‖*‖u a‖*‖u b‖)*
        (‖m 0‖*(‖m n.succ‖*‖m a.succ‖*‖m b.succ‖)) := by ring
    _ = _ := by
      rw [hp (fun i=>‖m i.succ‖)]
      simp only [Fin.prod_univ_succ,Fin.prod_univ_zero]
      change (4*oneYConstant hR*‖referenceContinuous hR.le*u n‖*‖u a‖*‖u b‖)*
        (‖m 0‖*(‖m 1‖*‖m 2‖*‖m 3‖))=
        (4*oneYConstant hR*‖referenceContinuous hR.le*u n‖*‖u a‖*‖u b‖)*
        (‖m 0‖*(‖m 1‖*(‖m 2‖*(‖m 3‖*1))))
      ring

theorem coefficientMap_first_oneY {R : ℝ} (hR : 0<R) (u : Fin 3→X R) :
    ‖coefficientMap R hR.le u‖≤4*oneYConstant hR*
      ‖referenceContinuous hR.le*u 0‖*‖u 1‖*‖u 2‖ :=
  coefficientMap_norm_from_slot hR 0 1 2 (fun _=>rfl) (collision_first_oneY hR) u

theorem coefficientMap_second_oneY {R : ℝ} (hR : 0<R) (u : Fin 3→X R) :
    ‖coefficientMap R hR.le u‖≤4*oneYConstant hR*
      ‖referenceContinuous hR.le*u 1‖*‖u 0‖*‖u 2‖ :=
  coefficientMap_norm_from_slot hR 1 0 2 (fun _=>by ring) (collision_second_oneY hR) u

theorem coefficientMap_third_oneY {R : ℝ} (hR : 0<R) (u : Fin 3→X R) :
    ‖coefficientMap R hR.le u‖≤4*oneYConstant hR*
      ‖referenceContinuous hR.le*u 2‖*‖u 0‖*‖u 1‖ :=
  coefficientMap_norm_from_slot hR 2 0 1 (fun _=>by ring) (collision_third_oneY hR) u

end
end Resonance.CubicParameterCoefficients
