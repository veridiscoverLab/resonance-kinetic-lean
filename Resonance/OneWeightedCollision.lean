import Resonance.OneWeightedParent

/-! All original cubic parents, with their original signs, satisfy a
one-weighted-input estimate in each of the three input positions. -/
open MeasureTheory Set
open scoped BigOperators
namespace Resonance.OneWeightedCollision
noncomputable section
set_option maxHeartbeats 1800000
open ResonantMeasure CollisionMultilinear OneWeightedParent OneWeightedPairReadout

theorem parent_first_second (R : ℝ) (hR : 0≤R) (l i j : Fin 4) (u g h : C(cube R,ℝ)) :
    parent R hR l i j u g h=parent R hR i l j g u h := by
  ext k
  change (∫q,parentTest R l i j u g h q∂CollisionFiber.fiberMeasure R k)=
    ∫q,parentTest R i l j g u h q∂CollisionFiber.fiberMeasure R k
  apply integral_congr_ae
  apply ae_of_all
  intro q
  simp only [parentTest,pointParent_apply,Fin.prod_univ_succ,Fin.prod_univ_zero,mul_one,
    Matrix.cons_val_zero,Matrix.cons_val_succ]
  ring

theorem parent_third_first (R : ℝ) (hR : 0≤R) (l i j : Fin 4) (u g h : C(cube R,ℝ)) :
    parent R hR l i j u g h=parent R hR j l i h u g := by
  ext k
  change (∫q,parentTest R l i j u g h q∂CollisionFiber.fiberMeasure R k)=
    ∫q,parentTest R j l i h u g q∂CollisionFiber.fiberMeasure R k
  apply integral_congr_ae
  apply ae_of_all
  intro q
  simp only [parentTest,pointParent_apply,Fin.prod_univ_succ,Fin.prod_univ_zero,mul_one,
    Matrix.cons_val_zero,Matrix.cons_val_succ]
  ring

theorem parentContinuous_as_parent (R : ℝ) (hR : 0≤R) (legs : Fin 3→Fin 4)
    (m : Fin 3→C(cube R,ℝ)) :
    parentContinuous R hR legs m=parent R hR (legs 0) (legs 1) (legs 2) (m 0) (m 1) (m 2) := by
  have hl : legs=![legs 0,legs 1,legs 2] := by ext i; fin_cases i <;> rfl
  have hm : m=![m 0,m 1,m 2] := by ext i; fin_cases i <;> rfl
  change parentContinuous R hR legs m=parentContinuous R hR _ _
  conv_lhs => rw [hl,hm]

theorem parent_first_bound {R : ℝ} (hR : 0<R) (legs : Fin 3→Fin 4)
    (m : Fin 3→C(cube R,ℝ)) :
    ‖parentContinuous R hR.le legs m‖≤oneYConstant hR*
      ‖referenceContinuous hR.le*m 0‖*‖m 1‖*‖m 2‖ := by
  rw [parentContinuous_as_parent]
  exact parent_oneY_bound hR _ _ _ _ _ _

theorem parent_second_bound {R : ℝ} (hR : 0<R) (legs : Fin 3→Fin 4)
    (m : Fin 3→C(cube R,ℝ)) :
    ‖parentContinuous R hR.le legs m‖≤oneYConstant hR*
      ‖referenceContinuous hR.le*m 1‖*‖m 0‖*‖m 2‖ := by
  rw [parentContinuous_as_parent,parent_first_second]
  exact parent_oneY_bound hR _ _ _ _ _ _

theorem parent_third_bound {R : ℝ} (hR : 0<R) (legs : Fin 3→Fin 4)
    (m : Fin 3→C(cube R,ℝ)) :
    ‖parentContinuous R hR.le legs m‖≤oneYConstant hR*
      ‖referenceContinuous hR.le*m 2‖*‖m 0‖*‖m 1‖ := by
  rw [parentContinuous_as_parent,parent_third_first]
  exact parent_oneY_bound hR _ _ _ _ _ _

theorem four_signed_bound {A : Type*} [SeminormedAddCommGroup A]
    (a b c d : A) {B : ℝ} (ha : ‖a‖≤B) (hb : ‖b‖≤B) (hc : ‖c‖≤B) (hd : ‖d‖≤B) :
    ‖a+b-c-d‖≤4*B := by
  have h1 := norm_sub_le (a+b-c) d
  have h2 := norm_sub_le (a+b) c
  have h3 := norm_add_le a b
  linarith

theorem collision_first_oneY {R : ℝ} (hR : 0<R) (m : Fin 3→C(cube R,ℝ)) :
    ‖collisionTrilinear R hR.le m‖≤4*oneYConstant hR*
      ‖referenceContinuous hR.le*m 0‖*‖m 1‖*‖m 2‖ := by
  exact (four_signed_bound _ _ _ _ (parent_first_bound hR ![1,2,3] m)
    (parent_first_bound hR ![0,2,3] m) (parent_first_bound hR ![0,1,3] m)
      (parent_first_bound hR ![0,1,2] m)).trans_eq (by ring)

theorem collision_second_oneY {R : ℝ} (hR : 0<R) (m : Fin 3→C(cube R,ℝ)) :
    ‖collisionTrilinear R hR.le m‖≤4*oneYConstant hR*
      ‖referenceContinuous hR.le*m 1‖*‖m 0‖*‖m 2‖ := by
  exact (four_signed_bound _ _ _ _ (parent_second_bound hR ![1,2,3] m)
    (parent_second_bound hR ![0,2,3] m) (parent_second_bound hR ![0,1,3] m)
      (parent_second_bound hR ![0,1,2] m)).trans_eq (by ring)

theorem collision_third_oneY {R : ℝ} (hR : 0<R) (m : Fin 3→C(cube R,ℝ)) :
    ‖collisionTrilinear R hR.le m‖≤4*oneYConstant hR*
      ‖referenceContinuous hR.le*m 2‖*‖m 0‖*‖m 1‖ := by
  exact (four_signed_bound _ _ _ _ (parent_third_bound hR ![1,2,3] m)
    (parent_third_bound hR ![0,2,3] m) (parent_third_bound hR ![0,1,3] m)
      (parent_third_bound hR ![0,1,2] m)).trans_eq (by ring)

end
end Resonance.OneWeightedCollision
