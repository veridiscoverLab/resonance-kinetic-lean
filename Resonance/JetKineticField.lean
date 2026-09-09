import Resonance.JetTransport
import Resonance.KineticUniqueness

/-! The original collision/transport vector field on the actual closed spatial
C³ jet space. The readback is the original KineticField, not another equation. -/
open Set Metric
open scoped NNReal
namespace Resonance.JetKineticField
noncomputable section
open JetCollision
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 30000

def field (R : ℝ) (hR : 0≤R) (c t : ℝ) (p : Space R) : Space R :=
  c • JetTransport.map R (-t) (collision R hR (JetTransport.map R t p))

theorem field_readback (R : ℝ) (hR : 0≤R) (c t : ℝ) (p : Space R) :
    readback (field R hR c t p)=KineticField.field R hR c t (readback p) := by
  simp only [field,readback_smul,JetTransport.map_readback,collision_readback,KineticField.field]

theorem field_joint_continuous (R : ℝ) (hR : 0≤R) (c : ℝ) :
    Continuous (fun q : ℝ × Space R => field R hR c q.1 q.2) := by
  unfold field
  apply Continuous.const_smul
  exact (JetTransport.map_joint_continuous R).comp (continuous_fst.neg.prodMk
    (((collision_contDiff R hR ⊤).continuous).comp (JetTransport.map_joint_continuous R)))

theorem field_norm_le (R : ℝ) (hR : 0≤R) (c t : ℝ) (p : Space R) :
    ‖field R hR c t p‖ ≤ |c| * ‖trilinear R hR‖ * ‖p‖^3 := by
  unfold field
  rw [norm_smul,Real.norm_eq_abs,JetTransport.map_norm]
  have h := mul_le_mul_of_nonneg_left (collision_norm_le R hR (JetTransport.map R t p)) (abs_nonneg c)
  simpa only [JetTransport.map_norm,mul_assoc] using h

theorem field_sub_norm_le {R M : ℝ} (hR : 0≤R) (hM : 0≤M) (c t : ℝ)
    (p q : Space R) (hp : ‖p‖≤M) (hq : ‖q‖≤M) :
    ‖field R hR c t p-field R hR c t q‖≤
      (|c| * (3*‖trilinear R hR‖*M^2))*‖p-q‖ := by
  unfold field
  rw [← smul_sub,norm_smul,Real.norm_eq_abs]
  change |c| * ‖JetTransport.operator R (-t) (collision R hR (JetTransport.map R t p))-
    JetTransport.operator R (-t) (collision R hR (JetTransport.map R t q))‖≤_
  rw [← map_sub]
  change |c| * ‖JetTransport.map R (-t) (collision R hR (JetTransport.map R t p)-
    collision R hR (JetTransport.map R t q))‖≤_
  rw [JetTransport.map_norm]
  have hd : ‖JetTransport.map R t p-JetTransport.map R t q‖=‖p-q‖ := by
    change ‖JetTransport.operator R t p-JetTransport.operator R t q‖=_
    rw [← map_sub]
    exact JetTransport.map_norm R t (p-q)
  have h := collision_sub_norm_le hR hM (JetTransport.map R t p) (JetTransport.map R t q)
    (by simpa only [JetTransport.map_norm] using hp) (by simpa only [JetTransport.map_norm] using hq)
  rw [hd] at h
  exact (mul_le_mul_of_nonneg_left h (abs_nonneg c)).trans_eq (mul_assoc _ _ _).symm

def sizeBound (R : ℝ) (hR : 0≤R) (c : ℝ) (p₀ : Space R) (a : ℝ≥0) : ℝ≥0 :=
  ⟨|c| * ‖trilinear R hR‖*(‖p₀‖+a)^3,by positivity⟩

def lipschitzBound (R : ℝ) (hR : 0≤R) (c : ℝ) (p₀ : Space R) (a : ℝ≥0) : ℝ≥0 :=
  ⟨|c| * (3*‖trilinear R hR‖*(‖p₀‖+a)^2),by positivity⟩

theorem norm_le_of_mem_ball {R : ℝ} (p₀ p : Space R) (a : ℝ≥0)
    (hp : p∈closedBall p₀ (a : ℝ)) : ‖p‖≤‖p₀‖+a := by
  have hd : ‖p-p₀‖≤a := by simpa [mem_closedBall,dist_eq_norm] using hp
  have h := norm_le_norm_sub_add p p₀
  linarith

theorem field_lipschitz_ball (R : ℝ) (hR : 0≤R) (c t : ℝ) (p₀ : Space R) (a : ℝ≥0) :
    LipschitzOnWith (lipschitzBound R hR c p₀ a) (field R hR c t) (closedBall p₀ a) := by
  apply lipschitzOnWith_iff_dist_le_mul.mpr
  intro p hp q hq
  simpa only [dist_eq_norm,lipschitzBound,NNReal.coe_mk] using
    field_sub_norm_le hR (show 0≤‖p₀‖+(a : ℝ) by positivity) c t p q
      (norm_le_of_mem_ball p₀ p a hp) (norm_le_of_mem_ball p₀ q a hq)

theorem field_size_ball (R : ℝ) (hR : 0≤R) (c t : ℝ) (p₀ : Space R) (a : ℝ≥0)
    (p : Space R) (hp : p∈closedBall p₀ (a : ℝ)) :
    ‖field R hR c t p‖ ≤ sizeBound R hR c p₀ a := by
  apply (field_norm_le R hR c t p).trans
  change |c| * ‖trilinear R hR‖*‖p‖^3 ≤ |c| * ‖trilinear R hR‖*(‖p₀‖+(a : ℝ))^3
  gcongr
  exact norm_le_of_mem_ball p₀ p a hp

def localTime (R : ℝ) (hR : 0≤R) (c : ℝ) (p₀ : Space R) (a : ℝ≥0) : ℝ :=
  (a : ℝ)/((sizeBound R hR c p₀ a : ℝ)+1)

theorem localTime_pos {R : ℝ} (hR : 0≤R) (c : ℝ) (p₀ : Space R)
    {a : ℝ≥0} (ha : 0<a) : 0<localTime R hR c p₀ a := by
  unfold localTime
  exact div_pos (by exact_mod_cast ha) (by positivity)

theorem localTime_size (R : ℝ) (hR : 0≤R) (c : ℝ) (p₀ : Space R) (a : ℝ≥0) :
    (sizeBound R hR c p₀ a : ℝ)*localTime R hR c p₀ a≤a := by
  unfold localTime
  rw [← mul_div_assoc]
  apply (div_le_iff₀ (by positivity : 0<(sizeBound R hR c p₀ a : ℝ)+1)).mpr
  nlinarith [a.coe_nonneg]

theorem actual_picardLindelof (R : ℝ) (hR : 0≤R) (c : ℝ)
    (p₀ : Space R) (a : ℝ≥0) (ha : 0<a) :
    IsPicardLindelof (field R hR c)
      (⟨0,le_rfl,(localTime_pos hR c p₀ ha).le⟩ : Icc 0 (localTime R hR c p₀ a))
      p₀ a 0 (sizeBound R hR c p₀ a) (lipschitzBound R hR c p₀ a) where
  lipschitzOnWith t _ := field_lipschitz_ball R hR c t p₀ a
  continuousOn p _ := ((field_joint_continuous R hR c).comp
    (continuous_id.prodMk continuous_const)).continuousOn
  norm_le t _ p hp := field_size_ball R hR c t p₀ a p hp
  mul_max_le := by
    simp only [sub_zero,NNReal.coe_zero,max_eq_left (localTime_pos hR c p₀ ha).le]
    exact localTime_size R hR c p₀ a

/-- Restart in the same absolute interaction clock. The field still contains
the original transport at time t, not a field reset at t₀. -/
theorem actual_picardLindelof_at (R : ℝ) (hR : 0≤R) (c t₀ : ℝ)
    (p₀ : Space R) (a : ℝ≥0) (ha : 0<a) :
    IsPicardLindelof (field R hR c)
      (⟨t₀,le_rfl,le_add_of_nonneg_right (localTime_pos hR c p₀ ha).le⟩ :
        Icc t₀ (t₀+localTime R hR c p₀ a))
      p₀ a 0 (sizeBound R hR c p₀ a) (lipschitzBound R hR c p₀ a) where
  lipschitzOnWith t _ := field_lipschitz_ball R hR c t p₀ a
  continuousOn p _ := ((field_joint_continuous R hR c).comp
    (continuous_id.prodMk continuous_const)).continuousOn
  norm_le t _ p hp := field_size_ball R hR c t p₀ a p hp
  mul_max_le := by
    simp only [add_sub_cancel_left,sub_self,NNReal.coe_zero,sub_zero,
      max_eq_left (localTime_pos hR c p₀ ha).le]
    exact localTime_size R hR c p₀ a

theorem localTime_lower_of_norm_le {R M : ℝ} (hR : 0≤R) (c : ℝ)
    (p₀ : Space R) (a : ℝ≥0) (hp : ‖p₀‖≤M) :
    (a : ℝ)/(|c| * ‖trilinear R hR‖*(M+a)^3+1) ≤ localTime R hR c p₀ a := by
  unfold localTime sizeBound
  apply div_le_div_of_nonneg_left a.coe_nonneg (by positivity)
  change |c| * ‖trilinear R hR‖*(‖p₀‖+(a : ℝ))^3+1 ≤
    |c| * ‖trilinear R hR‖*(M+(a : ℝ))^3+1
  gcongr

end
end Resonance.JetKineticField

#check Resonance.JetKineticField.field_readback
#print axioms Resonance.JetKineticField.field_readback
#check Resonance.JetKineticField.field_joint_continuous
#print axioms Resonance.JetKineticField.field_joint_continuous
#check Resonance.JetKineticField.field_norm_le
#print axioms Resonance.JetKineticField.field_norm_le
#check Resonance.JetKineticField.field_sub_norm_le
#print axioms Resonance.JetKineticField.field_sub_norm_le
#check Resonance.JetKineticField.norm_le_of_mem_ball
#print axioms Resonance.JetKineticField.norm_le_of_mem_ball
#check Resonance.JetKineticField.field_lipschitz_ball
#print axioms Resonance.JetKineticField.field_lipschitz_ball
#check Resonance.JetKineticField.field_size_ball
#print axioms Resonance.JetKineticField.field_size_ball
#check Resonance.JetKineticField.localTime_pos
#print axioms Resonance.JetKineticField.localTime_pos
#check Resonance.JetKineticField.localTime_size
#print axioms Resonance.JetKineticField.localTime_size
#check Resonance.JetKineticField.actual_picardLindelof
#print axioms Resonance.JetKineticField.actual_picardLindelof
#check Resonance.JetKineticField.actual_picardLindelof_at
#print axioms Resonance.JetKineticField.actual_picardLindelof_at
#check Resonance.JetKineticField.localTime_lower_of_norm_le
#print axioms Resonance.JetKineticField.localTime_lower_of_norm_le
