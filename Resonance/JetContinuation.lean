import Resonance.JetAmplitudeBounds
import Mathlib.Topology.Piecewise

/-! Same-clock continuation of the original compatible C³ kinetic path.
The complete time integral is preserved across the joining time. -/
open Set MeasureTheory
open scoped Interval
namespace Resonance.JetContinuation
noncomputable section
open JetCollision JetAmplitudeBounds JetKineticField FreeTransport
set_option maxHeartbeats 1500000
set_option synthInstance.maxHeartbeats 50000

section GeneralJoin
variable {E : Type*}

def join (T : ℝ) (g q : ℝ → E) (t : ℝ) : E :=
  if t ≤ T then g t else q t

theorem join_left {T : ℝ} (g q : ℝ → E) {t : ℝ} (ht : t ≤ T) :
    join T g q t=g t := if_pos ht

theorem join_right {T : ℝ} (g q : ℝ → E) (he : q T=g T)
    {t : ℝ} (ht : T ≤ t) : join T g q t=q t := by
  rcases eq_or_lt_of_le ht with h | h
  · subst t
    simp only [join,le_refl,ite_true,he]
  · exact if_neg (not_le.mpr h)

variable [NormedAddCommGroup E]

theorem join_continuousOn {T U : ℝ} (hT : 0 ≤ T) (hU : T ≤ U)
    (g q : ℝ → E) (hg : ContinuousOn g (Icc 0 T))
    (hq : ContinuousOn q (Icc T U)) (he : q T=g T) :
    ContinuousOn (join T g q) (Icc 0 U) := by
  have hg' : ContinuousOn (join T g q) (Icc 0 T) :=
    hg.congr (fun t ht => join_left g q ht.2)
  have hq' : ContinuousOn (join T g q) (Icc T U) :=
    hq.congr (fun t ht => join_right g q he ht.1)
  have h := hg'.union_of_isClosed hq' isClosed_Icc isClosed_Icc
  have hu : Icc (0 : ℝ) T ∪ Icc T U = Icc 0 U := by
    ext t
    constructor
    · rintro (ht | ht)
      · exact ⟨ht.1,ht.2.trans hU⟩
      · exact ⟨hT.trans ht.1,ht.2⟩
    · intro ht
      by_cases h : t ≤ T
      · exact Or.inl ⟨ht.1,h⟩
      · exact Or.inr ⟨(lt_of_not_ge h).le,ht.2⟩
  rwa [hu] at h

variable [NormedSpace ℝ E]

theorem join_integral_equation {T U : ℝ} (hT : 0 ≤ T) (hU : T ≤ U)
    (F : ℝ → E → E) (hFc : Continuous (fun x : ℝ × E => F x.1 x.2))
    (p₀ : E) (g q : ℝ → E)
    (hg : ContinuousOn g (Icc 0 T)) (hq : ContinuousOn q (Icc T U))
    (hjoin : q T=g T)
    (hge : ∀ t ∈ Icc 0 T,g t=p₀+∫ s in (0 : ℝ)..t,F s (g s))
    (hqe : ∀ t ∈ Icc T U,q t=g T+∫ s in T..t,F s (q s)) :
    ∀ t ∈ Icc 0 U,join T g q t=p₀+
      ∫ s in (0 : ℝ)..t,F s (join T g q s) := by
  let v : ℝ → E := join T g q
  have hv := join_continuousOn hT hU g q hg hq hjoin
  have hF : ContinuousOn (fun s => F s (v s)) (Icc 0 U) :=
    hFc.comp_continuousOn
      (continuous_id.continuousOn.prodMk hv)
  have hleft : ∀ t ∈ Icc 0 T,
      (∫ s in (0 : ℝ)..t,F s (v s))=
        ∫ s in (0 : ℝ)..t,F s (g s) := by
    intro t ht
    apply intervalIntegral.integral_congr
    intro s hs
    rw [uIcc_of_le ht.1] at hs
    change F s (v s)=F s (g s)
    rw [show v s=g s from join_left g q (hs.2.trans ht.2)]
  have hright : ∀ t ∈ Icc T U,
      (∫ s in T..t,F s (v s))=
        ∫ s in T..t,F s (q s) := by
    intro t ht
    apply intervalIntegral.integral_congr
    intro s hs
    rw [uIcc_of_le ht.1] at hs
    change F s (v s)=F s (q s)
    rw [show v s=q s from join_right g q hjoin hs.1]
  intro t ht
  by_cases h : t ≤ T
  · rw [join_left g q h]
    change g t=p₀+∫ s in (0 : ℝ)..t,F s (v s)
    rw [hleft t ⟨ht.1,h⟩]
    exact hge t ⟨ht.1,h⟩
  · have hTt : T ≤ t := (lt_of_not_ge h).le
    have hi0 : IntervalIntegrable (fun s => F s (v s)) volume 0 T :=
      (hF.mono (by rw [uIcc_of_le hT]; exact Icc_subset_Icc le_rfl hU)).intervalIntegrable
    have hiT : IntervalIntegrable (fun s => F s (v s)) volume T t :=
      (hF.mono (by rw [uIcc_of_le hTt]; exact Icc_subset_Icc hT ht.2)).intervalIntegrable
    rw [join_right g q hjoin hTt]
    change q t=p₀+∫ s in (0 : ℝ)..t,F s (v s)
    rw [← intervalIntegral.integral_add_adjacent_intervals hi0 hiT,
      hleft T ⟨hT,le_rfl⟩,hright t ⟨hTt,ht.2⟩,
      ← add_assoc,← hge T ⟨hT,le_rfl⟩]
    exact hqe t ⟨hTt,ht.2⟩

end GeneralJoin

def extensionTime (R : ℝ) (hR : 0 ≤ R) (c B : ℝ) : ℝ :=
  1/(|c| * ‖JetCollision.trilinear R hR‖*(B+1)^3+1)

theorem extensionTime_pos {R B : ℝ} (hR : 0 ≤ R) (c : ℝ) (hB : 0 ≤ B) :
    0 < extensionTime R hR c B := by
  unfold extensionTime
  positivity

theorem moving_frame_extension {R T B : ℝ} (hR : 0 ≤ R) (hT : 0 ≤ T) (hB : 0 ≤ B)
    (c : ℝ) (p₀ : Space R) (g : ℝ → Space R)
    (hg : ContinuousOn g (Icc 0 T))
    (he : ∀ t ∈ Icc 0 T,g t=p₀+∫ s in (0 : ℝ)..t,field R hR c s (g s))
    (hb : ‖g T‖ ≤ B) :
    ∃ v : ℝ → Space R, ContinuousOn v (Icc 0 (T+extensionTime R hR c B)) ∧
      EqOn v g (Icc 0 T) ∧
      ∀ t ∈ Icc 0 (T+extensionTime R hR c B),v t=p₀+
        ∫ s in (0 : ℝ)..t,field R hR c s (v s) := by
  obtain ⟨q,hqc,hqT,hqb,hqe⟩ := JetLocalKinetics.exists_moving_frame_solution_at R hR c T
    (g T) 1 (by norm_num)
  have htime : extensionTime R hR c B ≤ localTime R hR c (g T) 1 := by
    simpa only [extensionTime,NNReal.coe_one] using
      localTime_lower_of_norm_le hR c (g T) (a := 1) hb
  have hU : T ≤ T+extensionTime R hR c B :=
    le_add_of_nonneg_right (extensionTime_pos hR c hB).le
  have hqr : ∀ t ∈ Icc T (T+extensionTime R hR c B),
      q t=g T+∫ s in T..t,field R hR c s (q s) := by
    intro t ht
    exact hqe t ⟨ht.1,ht.2.trans (add_le_add_right htime T)⟩
  refine ⟨join T g q,join_continuousOn hT hU g q hg hqc.continuousOn hqT,?_,?_⟩
  · intro t ht
    exact join_left g q ht.2
  · exact join_integral_equation hT hU (field R hR c) (field_joint_continuous R hR c)
      p₀ g q hg hqc.continuousOn hqT he hqr

theorem moving_frame_to_actual_mild {R T : ℝ} (hR : 0 ≤ R) (c : ℝ)
    (p₀ : Space R) (v : ℝ → Space R) (hv : ContinuousOn v (Icc 0 T))
    (he : ∀ t ∈ Icc 0 T,v t=p₀+∫ s in (0 : ℝ)..t,field R hR c s (v s)) :
    ∀ t ∈ Icc 0 T,readback (JetTransport.map R t (v t))=transport R t (readback p₀)+
      ∫ s in (0 : ℝ)..t,c • transport R (t-s)
        (SpatialCollision.collision R hR (readback (JetTransport.map R s (v s)))) := by
  intro t ht
  have hi : IntervalIntegrable (fun s => field R hR c s (v s)) volume 0 t :=
    (((field_joint_continuous R hR c).comp_continuousOn
      (continuous_id.continuousOn.prodMk hv)).mono
        (uIcc_subset_Icc ⟨le_rfl,ht.1.trans ht.2⟩ ht)).intervalIntegrable
  have hh := congrArg (JetLocalKinetics.readbackOperator R) (he t ht)
  rw [map_add,← (JetLocalKinetics.readbackOperator R).intervalIntegral_comp_comm hi] at hh
  change readback (v t)=readback p₀+
    ∫ s in (0 : ℝ)..t,readback (field R hR c s (v s)) at hh
  simp only [field_readback] at hh
  let F : ℝ → Distribution R := fun s => c • SpatialCollision.collision R hR
    (readback (JetTransport.map R s (v s)))
  have hp := (JetTransport.map_joint_continuous R).comp_continuousOn
    (continuous_id.continuousOn.prodMk hv)
  have hF : ContinuousOn F (uIcc 0 t) :=
    (((SpatialCollision.collision_continuous hR).comp_continuousOn
      ((readback_continuous R).comp_continuousOn hp)).const_smul c).mono
        (uIcc_subset_Icc ⟨le_rfl,ht.1.trans ht.2⟩ ht)
  have hh' : readback (v t)=readback p₀+
      ∫ s in (0 : ℝ)..t,transport R (-s) (F s) := by
    simpa only [F,JetTransport.map_readback,transport_smul,KineticField.field] using hh
  have h := TransportDuhamel.moving_frame_solution_to_duhamel R t (readback p₀)
    (g := fun s => readback (v s)) hF hh'
  simpa only [F,JetTransport.map_readback,transport_smul] using h

/-- A closed-time actual mild path can be continued on a uniform additional
interval controlled only by its amplitude and original C³ datum. -/
theorem actual_mild_extension {R T M : ℝ} (hR : 0 ≤ R) (hT : 0 ≤ T) (hM : 0 ≤ M)
    (c : ℝ) (p₀ : Space R) (p : ℝ → Space R) (hp : ContinuousOn p (Icc 0 T))
    (he : ∀ t ∈ Icc 0 T,readback (p t)=transport R t (readback p₀)+
      ∫ s in (0 : ℝ)..t,c • transport R (t-s)
        (SpatialCollision.collision R hR (readback (p s))))
    (hamp : ∀ t ∈ Icc 0 T,‖readback (p t)‖ ≤ M) :
    let τ := extensionTime R hR c (jetBudget R c M T p₀)
    0 < τ ∧ ∃ q : ℝ → Space R, ContinuousOn q (Icc 0 (T+τ)) ∧ EqOn q p (Icc 0 T) ∧
      ∀ t ∈ Icc 0 (T+τ),readback (q t)=transport R t (readback p₀)+
        ∫ s in (0 : ℝ)..t,c • transport R (t-s)
          (SpatialCollision.collision R hR (readback (q s))) := by
  let B := jetBudget R c M T p₀
  have hn := budgets_nonnegative (R := R) (c := c) hM hT p₀
  have hB : 0 ≤ B := by dsimp only [B,jetBudget]; linarith [hn.1,hn.2.2.1,hn.2.2.2.2]
  have hg := toFrame_continuousOn hp
  have hge := actual_mild_to_moving_frame hR c p₀ p hp he
  have hb : ‖toFrame R p T‖ ≤ B := by
    simpa only [toFrame,JetTransport.map_norm] using
      actual_mild_norm_bound hR hT hM c p₀ p hp he hamp T ⟨hT,le_rfl⟩
  obtain ⟨v,hv,hvp,hve⟩ := moving_frame_extension hR hT hB c p₀ (toFrame R p) hg hge hb
  refine ⟨extensionTime_pos hR c hB,fun t => JetTransport.map R t (v t),
    (JetTransport.map_joint_continuous R).comp_continuousOn
      (continuous_id.continuousOn.prodMk hv),?_,?_⟩
  · intro t ht
    change JetTransport.map R t (v t)=p t
    rw [hvp ht]
    change JetTransport.map R t (JetTransport.map R (-t) (p t))=p t
    rw [JetTransport.map_add_time,add_neg_cancel,JetTransport.map_zero_time]
  · exact moving_frame_to_actual_mild hR c p₀ v hv hve

end
end Resonance.JetContinuation

#check Resonance.JetContinuation.join_left
#check Resonance.JetContinuation.join_right
#check Resonance.JetContinuation.join_continuousOn
#check Resonance.JetContinuation.join_integral_equation
#check Resonance.JetContinuation.extensionTime_pos
#check Resonance.JetContinuation.moving_frame_extension
#check Resonance.JetContinuation.moving_frame_to_actual_mild
#check Resonance.JetContinuation.actual_mild_extension
#print axioms Resonance.JetContinuation.join_left
#print axioms Resonance.JetContinuation.join_right
#print axioms Resonance.JetContinuation.join_continuousOn
#print axioms Resonance.JetContinuation.join_integral_equation
#print axioms Resonance.JetContinuation.extensionTime_pos
#print axioms Resonance.JetContinuation.moving_frame_extension
#print axioms Resonance.JetContinuation.moving_frame_to_actual_mild
#print axioms Resonance.JetContinuation.actual_mild_extension
