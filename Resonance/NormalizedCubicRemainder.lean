import Resonance.TrilinearRemainderAlgebra
import Resonance.MacroCorrectorCollision

/-! Exact quadratic/cubic remainder of the same normalized collision,
and the one-Y difference estimate used by the regularized corrector. -/
open Set
open scoped BigOperators
namespace Resonance.NormalizedCubicRemainder
noncomputable section
set_option maxHeartbeats 2000000
open ResonantMeasure Thermodynamics ProfileBanachSmooth NormalizedCubicOneY
open OneWeightedPairReadout

def remainder (R : ℝ) (hR : 0≤R) (θ : Parameter) (q : X R) : X R :=
  TrilinearRemainderAlgebra.remainder (normalizedTrilinear R hR θ) 1 q

def linearPart (R : ℝ) (hR : 0≤R) (θ : Parameter) (q : X R) : X R :=
  TrilinearRemainderAlgebra.linearPart (normalizedTrilinear R hR θ) 1 q

theorem constant_vector (R : ℝ) (f : X R) : ![f,f,f]=(fun _ : Fin 3=>f) := by
  ext i
  fin_cases i <;> rfl

theorem actual_expansion (R : ℝ) (hR : 0≤R) (θ : Parameter) (q : X R) :
    denominatorMap R θ*FiberContinuity.collisionMap R hR (profileMap R θ*(1+q))=
      denominatorMap R θ*FiberContinuity.collisionMap R hR (profileMap R θ)+
        linearPart R hR θ q+remainder R hR θ q := by
  have h := TrilinearRemainderAlgebra.exact_expansion (normalizedTrilinear R hR θ) 1 q
  rw [constant_vector,constant_vector,normalizedTrilinear_diagonal,
    normalizedTrilinear_diagonal,mul_one] at h
  exact h

theorem first_small {R κ : ℝ} (hR : 0<R) (θ : Parameter) (u v w : X R)
    (hp : ‖v‖*‖w‖≤κ) :
    ‖normalizedTrilinear R hR.le θ ![u,v,w]‖≤
      oneYBound hR θ*κ*‖referenceContinuous hR.le*u‖ := by
  have hb := normalized_first_oneY hR θ ![u,v,w]
  simp only [Matrix.cons_val_zero] at hb
  calc
    _ ≤ oneYBound hR θ*‖referenceContinuous hR.le*u‖*‖v‖*‖w‖ := hb
    _ = (oneYBound hR θ*‖referenceContinuous hR.le*u‖)*(‖v‖*‖w‖) := by ring
    _ ≤ (oneYBound hR θ*‖referenceContinuous hR.le*u‖)*κ :=
      mul_le_mul_of_nonneg_left hp (mul_nonneg (oneYBound_positive hR θ).le (norm_nonneg _))
    _ = _ := by ring

theorem second_small {R κ : ℝ} (hR : 0<R) (θ : Parameter) (u v w : X R)
    (hp : ‖v‖*‖w‖≤κ) :
    ‖normalizedTrilinear R hR.le θ ![v,u,w]‖≤
      oneYBound hR θ*κ*‖referenceContinuous hR.le*u‖ := by
  have hb := normalized_second_oneY hR θ ![v,u,w]
  simp only [Matrix.cons_val_zero] at hb
  calc
    _ ≤ oneYBound hR θ*‖referenceContinuous hR.le*u‖*‖v‖*‖w‖ := hb
    _ = (oneYBound hR θ*‖referenceContinuous hR.le*u‖)*(‖v‖*‖w‖) := by ring
    _ ≤ (oneYBound hR θ*‖referenceContinuous hR.le*u‖)*κ :=
      mul_le_mul_of_nonneg_left hp (mul_nonneg (oneYBound_positive hR θ).le (norm_nonneg _))
    _ = _ := by ring

theorem third_small {R κ : ℝ} (hR : 0<R) (θ : Parameter) (u v w : X R)
    (hp : ‖v‖*‖w‖≤κ) :
    ‖normalizedTrilinear R hR.le θ ![v,w,u]‖≤
      oneYBound hR θ*κ*‖referenceContinuous hR.le*u‖ := by
  have hb := normalized_third_oneY hR θ ![v,w,u]
  simp only [Matrix.cons_val_zero] at hb
  calc
    _ ≤ oneYBound hR θ*‖referenceContinuous hR.le*u‖*‖v‖*‖w‖ := hb
    _ = (oneYBound hR θ*‖referenceContinuous hR.le*u‖)*(‖v‖*‖w‖) := by ring
    _ ≤ (oneYBound hR θ*‖referenceContinuous hR.le*u‖)*κ :=
      mul_le_mul_of_nonneg_left hp (mul_nonneg (oneYBound_positive hR θ).le (norm_nonneg _))
    _ = _ := by ring

theorem one_norm_le (R : ℝ) : ‖(1 : X R)‖≤1 := by
  apply (ContinuousMap.norm_le _ (by norm_num)).mpr
  intro k
  change ‖(1:ℝ)‖≤1
  norm_num

theorem actual_remainder_oneY_lipschitz {R κ : ℝ} (hR : 0<R) (θ : Parameter)
    (hκ : κ≤1) (q r : X R) (hq : ‖q‖≤κ) (hr : ‖r‖≤κ) :
    ‖remainder R hR.le θ q-remainder R hR.le θ r‖≤
      9*oneYBound hR θ*κ*‖referenceContinuous hR.le*(q-r)‖ := by
  have hκ0 : 0≤κ := (norm_nonneg q).trans hq
  have hq1 : ‖q‖*‖(1:X R)‖≤κ :=
    (mul_le_mul hq (one_norm_le R) (norm_nonneg _) hκ0).trans_eq (mul_one κ)
  have hr1 : ‖r‖*‖(1:X R)‖≤κ :=
    (mul_le_mul hr (one_norm_le R) (norm_nonneg _) hκ0).trans_eq (mul_one κ)
  have h1q : ‖(1:X R)‖*‖q‖≤κ := (mul_comm _ _).trans_le hq1
  have h1r : ‖(1:X R)‖*‖r‖≤κ := (mul_comm _ _).trans_le hr1
  have hκsq : κ*κ≤κ := (mul_le_mul_of_nonneg_left hκ hκ0).trans_eq (mul_one κ)
  have hqq : ‖q‖*‖q‖≤κ := (mul_le_mul hq hq (norm_nonneg _) hκ0).trans hκsq
  have hrq : ‖r‖*‖q‖≤κ := (mul_le_mul hr hq (norm_nonneg _) hκ0).trans hκsq
  have hrr : ‖r‖*‖r‖≤κ := (mul_le_mul hr hr (norm_nonneg _) hκ0).trans hκsq
  have hb : ∀i : Fin 9,‖TrilinearRemainderAlgebra.differenceTerms
      (normalizedTrilinear R hR.le θ) 1 q r i‖≤
        oneYBound hR θ*κ*‖referenceContinuous hR.le*(q-r)‖ := by
    intro i
    fin_cases i
    · exact first_small hR θ (q-r) q 1 hq1
    · exact second_small hR θ (q-r) r 1 hr1
    · exact first_small hR θ (q-r) 1 q h1q
    · exact third_small hR θ (q-r) r 1 hr1
    · exact second_small hR θ (q-r) 1 q h1q
    · exact third_small hR θ (q-r) 1 r h1r
    · exact first_small hR θ (q-r) q q hqq
    · exact second_small hR θ (q-r) r q hrq
    · exact third_small hR θ (q-r) r r hrr
  exact (TrilinearRemainderAlgebra.norm_difference_le _ hb).trans_eq (by ring)

theorem linearPart_actual_derivative (R : ℝ) (hR : 0≤R) (θ : Parameter) (q : X R) :
    linearPart R hR θ q=denominatorMap R θ*
      fderiv ℝ (FiberContinuity.collisionMap R hR) (profileMap R θ) (profileMap R θ*q) := by
  have hv (a b c : X R) : (fun i : Fin 3=>profileMap R θ*![a,b,c] i)=
      ![profileMap R θ*a,profileMap R θ*b,profileMap R θ*c] := by
    ext i
    fin_cases i <;> rfl
  simp only [linearPart,TrilinearRemainderAlgebra.linearPart,normalizedTrilinear_apply,
    hv,mul_one,MacroCorrectorCollision.full_derivative_three_slots,mul_add]

theorem remainder_zero (R : ℝ) (hR : 0≤R) (θ : Parameter) : remainder R hR θ 0=0 := by
  have he := actual_expansion R hR θ 0
  rw [add_zero,mul_one,linearPart_actual_derivative,mul_zero,map_zero,mul_zero,add_zero] at he
  exact add_eq_left.mp he.symm

theorem actual_remainder_oneY_bound {R κ : ℝ} (hR : 0<R) (θ : Parameter)
    (hκ : κ≤1) (q : X R) (hq : ‖q‖≤κ) :
    ‖remainder R hR.le θ q‖≤9*oneYBound hR θ*κ*‖referenceContinuous hR.le*q‖ := by
  have hb := actual_remainder_oneY_lipschitz hR θ hκ q 0 hq
    (by simpa only [norm_zero] using (norm_nonneg q).trans hq)
  simpa only [remainder_zero,sub_zero] using hb

theorem profileMap_eq_rj {R : ℝ} {θ : Parameter} (hθ : θ∈positiveDomain R) :
    profileMap R θ=ContinuousCollisionForm.rjCube hθ := by
  ext k
  exact profileMap_apply hθ k

theorem actual_rj_zero {R : ℝ} (hR : 0≤R) {θ : Parameter} (hθ : θ∈positiveDomain R) :
    FiberContinuity.collisionMap R hR (profileMap R θ)=0 := by
  rw [profileMap_eq_rj hθ]
  exact MacroCorrectorCollision.actual_rj_collision_zero hR hθ

theorem actual_normalized_decomposition {R : ℝ} (hR : 0≤R) {θ : Parameter}
    (hθ : θ∈positiveDomain R) (q : X R) :
    denominatorMap R θ*FiberContinuity.collisionMap R hR (profileMap R θ*(1+q))=
      denominatorMap R θ*fderiv ℝ (FiberContinuity.collisionMap R hR)
        (profileMap R θ) (profileMap R θ*q)+remainder R hR θ q := by
  rw [actual_expansion,actual_rj_zero hR hθ,mul_zero,zero_add,linearPart_actual_derivative]

theorem oneYBound_continuousAt {R : ℝ} (hR : 0<R) {θ : Parameter}
    (hθ : θ∈positiveDomain R) : ContinuousAt (oneYBound hR) θ := by
  have hn := (profileMap_contDiffAt hθ).continuousAt
  unfold oneYBound
  fun_prop

theorem compact_oneYBound {R : ℝ} (hR : 0<R) {K : Set Parameter} (hK : IsCompact K)
    (hpos : K⊆positiveDomain R) : ∃C>0,∀θ∈K,oneYBound hR θ≤C := by
  have hc : ContinuousOn (oneYBound hR) K :=
    fun θ hθ=>(oneYBound_continuousAt hR (hpos hθ)).continuousWithinAt
  obtain ⟨M,hM⟩ := hK.bddAbove_image hc
  refine ⟨|M|+1,by positivity,?_⟩
  intro θ hθ
  exact (hM ⟨θ,hθ,rfl⟩).trans ((le_abs_self M).trans (le_add_of_nonneg_right (by norm_num)))

theorem actual_compact_remainder_oneY {R : ℝ} (hR : 0<R) {K : Set Parameter}
    (hK : IsCompact K) (hpos : K⊆positiveDomain R) :
    ∃C>0,∀θ∈K,∀κ : ℝ,κ≤1→∀q r : X R,‖q‖≤κ→‖r‖≤κ→
      ‖remainder R hR.le θ q-remainder R hR.le θ r‖≤
        C*κ*‖referenceContinuous hR.le*(q-r)‖ := by
  obtain ⟨C,hC,hbound⟩ := compact_oneYBound hR hK hpos
  refine ⟨9*C,by positivity,?_⟩
  intro θ hθ κ hκ q r hq hr
  have hκ0 := (norm_nonneg q).trans hq
  apply (actual_remainder_oneY_lipschitz hR θ hκ q r hq hr).trans
  gcongr
  exact hbound θ hθ

end
end Resonance.NormalizedCubicRemainder
