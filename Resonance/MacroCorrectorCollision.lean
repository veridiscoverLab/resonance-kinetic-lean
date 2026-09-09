import Resonance.ContinuousCollisionForm

/-! The same corrector G in two actual RJ backgrounds. All original cubic
parents are retained; the pure cubic G term cancels before any estimate.
The identities here do not assume a one-Y estimate for the surviving terms. -/
open Set MeasureTheory Function
namespace Resonance.MacroCorrectorCollision
noncomputable section
open ResonantMeasure FreeTransport FiberContinuity CollisionFiber CollisionPositivity
open ContinuousCollisionForm CollisionMultilinear CollisionLinearization
set_option maxHeartbeats 1500000

abbrev CubeFunction (R : ℝ) := C(MomentumDomain R,ℝ)

theorem constant_three {A : Type*} (a : A) : (fun _ : Fin 3=>a)=![a,a,a] := by
  funext i
  fin_cases i <;> rfl

theorem triple_add_first {R : ℝ} (hR : 0≤R) (a b d e : CubeFunction R) :
    collisionTrilinear R hR ![a+e,b,d]=
      collisionTrilinear R hR ![a,b,d]+collisionTrilinear R hR ![e,b,d] := by
  simpa only [JetCollision.update_three_zero] using
    (collisionTrilinear R hR).map_update_add ![0,b,d] 0 a e

theorem triple_add_second {R : ℝ} (hR : 0≤R) (a b d e : CubeFunction R) :
    collisionTrilinear R hR ![a,b+e,d]=
      collisionTrilinear R hR ![a,b,d]+collisionTrilinear R hR ![a,e,d] := by
  simpa only [JetCollision.update_three_one] using
    (collisionTrilinear R hR).map_update_add ![a,0,d] 1 b e

theorem triple_add_third {R : ℝ} (hR : 0≤R) (a b d e : CubeFunction R) :
    collisionTrilinear R hR ![a,b,d+e]=
      collisionTrilinear R hR ![a,b,d]+collisionTrilinear R hR ![a,b,e] := by
  simpa only [JetCollision.update_three_two] using
    (collisionTrilinear R hR).map_update_add ![a,b,0] 2 d e

theorem full_derivative_three_slots {R : ℝ} (hR : 0≤R) (N G : CubeFunction R) :
    fderiv ℝ (collisionMap R hR) N G=collisionTrilinear R hR ![G,N,N]+
      collisionTrilinear R hR ![N,G,N]+collisionTrilinear R hR ![N,N,G] := by
  rw [collisionMap_fderiv_apply,constant_three N]
  simp [Fin.sum_univ_succ,JetCollision.update_three_zero,JetCollision.update_three_one,
    JetCollision.update_three_two,add_assoc]

theorem actual_collision_cubic_add {R : ℝ} (hR : 0≤R) (N G : CubeFunction R) :
    collisionMap R hR (N+G)=collisionMap R hR N+
      fderiv ℝ (collisionMap R hR) N G+fderiv ℝ (collisionMap R hR) G N+
        collisionMap R hR G := by
  rw [←collisionTrilinear_diagonal hR (N+G),←collisionTrilinear_diagonal hR N,
    ←collisionTrilinear_diagonal hR G,full_derivative_three_slots,full_derivative_three_slots]
  simp_rw [constant_three (N+G),constant_three N,constant_three G,
    triple_add_first,triple_add_second,triple_add_third]
  abel

/-- Both endpoints use the same G. Every summand on the right contains G;
the pure G cubic is absent because it cancels exactly in the actual map. -/
theorem actual_common_corrector_double_difference {R : ℝ} (hR : 0≤R)
    (N M G : CubeFunction R) :
    collisionMap R hR (N+G)-collisionMap R hR (M+G)-
      collisionMap R hR N+collisionMap R hR M=
        (fderiv ℝ (collisionMap R hR) N-fderiv ℝ (collisionMap R hR) M) G+
          fderiv ℝ (collisionMap R hR) G (N-M) := by
  rw [actual_collision_cubic_add,actual_collision_cubic_add,map_sub]
  simp only [ContinuousLinearMap.sub_apply]
  abel

theorem actual_rj_collision_zero {R : ℝ} (hR : 0≤R) {θ : Thermodynamics.Parameter}
    (hθ : θ∈Thermodynamics.positiveDomain R) : collisionMap R hR (rjCube hθ)=0 := by
  ext k
  rw [collisionMap_apply R hR _ (WeightedJointMeasure.profile θ) (fun _=>rfl)]
  change (∫q,collisionIntegrand (WeightedJointMeasure.profile θ) q∂fiberMeasure R k)=0
  apply integral_eq_zero_of_ae
  filter_upwards [fiber_support R k,fiber_energy_zero R k,fiber_momentum_zero R k] with q hq he hm
  have hN : ∀i,WeightedJointMeasure.profile θ (q i)≠0 :=
    fun i=>(WeightedJointMeasure.profile_pos hθ (hq.1 i)).ne'
  have hmoment : q 0+q 1=q 2+q 3 := sub_eq_zero.mp (by simpa only [sub_sub] using hm)
  have henergy : ‖q 0‖^2+‖q 1‖^2=‖q 2‖^2+‖q 3‖^2 := by
    unfold CoareaNormalization.energy at he
    linarith
  have hd:=reciprocalProfile_full_relation θ q hmoment henergy
  simp only [WeightedPhysicalForm.reciprocalProfile_eq_inv] at hd
  rw [collisionIntegrand,Collision.collision_reciprocal_identity _ hN,hd,mul_zero]
  rfl

/-- The surviving macro difference for two genuine positive RJ states. -/
theorem actual_rj_common_corrector_difference {R : ℝ} (hR : 0≤R)
    {θ β : Thermodynamics.Parameter} (hθ : θ∈Thermodynamics.positiveDomain R)
    (hβ : β∈Thermodynamics.positiveDomain R) (G : CubeFunction R) :
    collisionMap R hR (rjCube hθ+G)-collisionMap R hR (rjCube hβ+G)=
      (fderiv ℝ (collisionMap R hR) (rjCube hθ)-
        fderiv ℝ (collisionMap R hR) (rjCube hβ)) G+
          fderiv ℝ (collisionMap R hR) G (rjCube hθ-rjCube hβ) := by
  simpa only [actual_rj_collision_zero hR hθ,actual_rj_collision_zero hR hβ,sub_zero,add_zero]
    using actual_common_corrector_double_difference hR (rjCube hθ) (rjCube hβ) G

/-- The collision term in the same coframe history: the actual microscopic
two-state difference plus the macro change with the common G held fixed. -/
theorem actual_micro_macro_decomposition {R : ℝ} (hR : 0≤R)
    {θ β : Thermodynamics.Parameter} (hθ : θ∈Thermodynamics.positiveDomain R)
    (hβ : β∈Thermodynamics.positiveDomain R) (f G : CubeFunction R) :
    collisionMap R hR f-collisionMap R hR (rjCube hβ+G)=
      (collisionMap R hR f-collisionMap R hR (rjCube hθ+G))+
        ((fderiv ℝ (collisionMap R hR) (rjCube hθ)-
          fderiv ℝ (collisionMap R hR) (rjCube hβ)) G+
            fderiv ℝ (collisionMap R hR) G (rjCube hθ-rjCube hβ)) := by
  rw [←actual_rj_common_corrector_difference hR hθ hβ G]
  abel

end
end Resonance.MacroCorrectorCollision

#check Resonance.MacroCorrectorCollision.constant_three
#check Resonance.MacroCorrectorCollision.triple_add_first
#check Resonance.MacroCorrectorCollision.triple_add_second
#check Resonance.MacroCorrectorCollision.triple_add_third
#check Resonance.MacroCorrectorCollision.full_derivative_three_slots
#check Resonance.MacroCorrectorCollision.actual_collision_cubic_add
#check Resonance.MacroCorrectorCollision.actual_common_corrector_double_difference
#check Resonance.MacroCorrectorCollision.actual_rj_collision_zero
#check Resonance.MacroCorrectorCollision.actual_rj_common_corrector_difference
#check Resonance.MacroCorrectorCollision.actual_micro_macro_decomposition
#print axioms Resonance.MacroCorrectorCollision.constant_three
#print axioms Resonance.MacroCorrectorCollision.triple_add_first
#print axioms Resonance.MacroCorrectorCollision.triple_add_second
#print axioms Resonance.MacroCorrectorCollision.triple_add_third
#print axioms Resonance.MacroCorrectorCollision.full_derivative_three_slots
#print axioms Resonance.MacroCorrectorCollision.actual_collision_cubic_add
#print axioms Resonance.MacroCorrectorCollision.actual_common_corrector_double_difference
#print axioms Resonance.MacroCorrectorCollision.actual_rj_collision_zero
#print axioms Resonance.MacroCorrectorCollision.actual_rj_common_corrector_difference
#print axioms Resonance.MacroCorrectorCollision.actual_micro_macro_decomposition
