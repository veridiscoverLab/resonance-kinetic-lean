import Resonance.JetKineticField

/-! Local compatible-C³ solutions read back to the original full mild equation.
Uniqueness in the original C phase-space class identifies the same solution. -/
open Set Metric MeasureTheory
open scoped NNReal Interval
namespace Resonance.JetLocalKinetics
noncomputable section
open JetCollision JetKineticField
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 30000

def readbackOperator (R : ℝ) : Space R →L[ℝ] FreeTransport.Distribution R :=
  SpatialJetSpace.toDistributionCLM R

theorem exists_moving_frame_solution (R : ℝ) (hR : 0≤R) (c : ℝ)
    (p₀ : Space R) (a : ℝ≥0) (ha : 0<a) :
    ∃ g : ℝ → Space R, Continuous g ∧ g 0=p₀ ∧
      (∀ t,‖g t-p₀‖≤a) ∧ ∀ t∈Icc 0 (localTime R hR c p₀ a),
        g t=p₀+∫ s in (0 : ℝ)..t,field R hR c s (g s) := by
  let hp := actual_picardLindelof R hR c p₀ a ha
  have hx : p₀∈closedBall p₀ (0 : ℝ) := mem_closedBall_self le_rfl
  obtain ⟨α,hα⟩ := ODE.FunSpace.exists_isFixedPt_next hp hx
  refine ⟨α.compProj,α.continuous_compProj,?_,?_,?_⟩
  · rw [ODE.FunSpace.compProj_of_mem (show 0∈Icc 0 (localTime R hR c p₀ a) from
      ⟨le_rfl,(localTime_pos hR c p₀ ha).le⟩)]
    exact α.apply_of_zero
  · intro t
    exact mem_closedBall_iff_norm.mp (α.compProj_mem_closedBall hp.mul_max_le)
  · intro t ht
    rw [ODE.FunSpace.compProj_of_mem ht]
    exact (ODE.FunSpace.isFixedPt_next_iff hp hx).mp hα ⟨t,ht⟩

/-- A compatible datum can be restarted at any absolute time. Together with
the uniform lower bound on localTime for a bounded jet ball, this is the
local continuation interface; no global bound on a solution is assumed. -/
theorem exists_moving_frame_solution_at (R : ℝ) (hR : 0≤R) (c t₀ : ℝ)
    (p₀ : Space R) (a : ℝ≥0) (ha : 0<a) :
    ∃ g : ℝ → Space R, Continuous g ∧ g t₀=p₀ ∧
      (∀ t,‖g t-p₀‖≤a) ∧ ∀ t∈Icc t₀ (t₀+localTime R hR c p₀ a),
        g t=p₀+∫ s in t₀..t,field R hR c s (g s) := by
  let hp := actual_picardLindelof_at R hR c t₀ p₀ a ha
  have hx : p₀∈closedBall p₀ (0 : ℝ) := mem_closedBall_self le_rfl
  obtain ⟨α,hα⟩ := ODE.FunSpace.exists_isFixedPt_next hp hx
  refine ⟨α.compProj,α.continuous_compProj,?_,?_,?_⟩
  · rw [ODE.FunSpace.compProj_of_mem (show t₀∈Icc t₀ (t₀+localTime R hR c p₀ a) from
      ⟨le_rfl,le_add_of_nonneg_right (localTime_pos hR c p₀ ha).le⟩)]
    exact α.apply_of_zero
  · intro t
    exact mem_closedBall_iff_norm.mp (α.compProj_mem_closedBall hp.mul_max_le)
  · intro t ht
    rw [ODE.FunSpace.compProj_of_mem ht]
    exact (ODE.FunSpace.isFixedPt_next_iff hp hx).mp hα ⟨t,ht⟩

theorem moving_frame_readback {R : ℝ} (hR : 0≤R) (c : ℝ) (p₀ : Space R)
    (g : ℝ → Space R) (hg : Continuous g) {t : ℝ}
    (he : g t=p₀+∫ s in (0 : ℝ)..t,field R hR c s (g s)) :
    readback (g t)=readback p₀+∫ s in (0 : ℝ)..t,KineticField.field R hR c s (readback (g s)) := by
  have hi : IntervalIntegrable (fun s => field R hR c s (g s)) volume 0 t :=
    ((field_joint_continuous R hR c).comp (continuous_id.prodMk hg)).intervalIntegrable _ _
  have h := congrArg (readbackOperator R) he
  rw [map_add,← (readbackOperator R).intervalIntegral_comp_comm hi] at h
  change readback (g t)=readback p₀+∫ s in (0 : ℝ)..t,readback (field R hR c s (g s)) at h
  simpa only [field_readback] using h

theorem exists_mild_jet_solution (R : ℝ) (hR : 0≤R) (c : ℝ)
    (p₀ : Space R) (a : ℝ≥0) (ha : 0<a) :
    ∃ p : ℝ → Space R, Continuous p ∧ p 0=p₀ ∧
      (∀ t,‖p t-JetTransport.map R t p₀‖≤a) ∧
      (∀ t,‖p t‖≤‖p₀‖+a) ∧
      (∀ t,ContDiff ℝ 3 (SpatialChainRule.realLift (readback (p t)))) ∧
      ∀ t∈Icc 0 (localTime R hR c p₀ a),
        readback (p t)=FreeTransport.transport R t (readback p₀)+
          ∫ s in (0 : ℝ)..t,c • FreeTransport.transport R (t-s)
            (SpatialCollision.collision R hR (readback (p s))) := by
  obtain ⟨g,hgc,hg0,hgb,hge⟩ := exists_moving_frame_solution R hR c p₀ a ha
  let p : ℝ → Space R := fun t => JetTransport.map R t (g t)
  have hpc : Continuous p := (JetTransport.map_joint_continuous R).comp (continuous_id.prodMk hgc)
  have hreadc : Continuous (fun t => readback (p t)) := (readback_continuous R).comp hpc
  refine ⟨p,hpc,?_,?_,?_,fun t => SpatialJetSpace.toDistribution_contDiff (p t),?_⟩
  · change JetTransport.map R 0 (g 0)=p₀
    rw [hg0,JetTransport.map_zero_time]
  · intro t
    change ‖JetTransport.operator R t (g t)-JetTransport.operator R t p₀‖≤a
    rw [← map_sub]
    change ‖JetTransport.map R t (g t-p₀)‖≤a
    rw [JetTransport.map_norm]
    exact hgb t
  · intro t
    change ‖JetTransport.map R t (g t)‖≤_
    rw [JetTransport.map_norm]
    have h := norm_le_norm_sub_add (g t) p₀
    linarith [hgb t]
  · intro t ht
    let F : ℝ → FreeTransport.Distribution R := fun s => c • SpatialCollision.collision R hR (readback (p s))
    have hF : Continuous F := ((SpatialCollision.collision_continuous hR).comp hreadc).const_smul c
    have he : readback (g t)=readback p₀+
        ∫ s in (0 : ℝ)..t,FreeTransport.transport R (-s) (F s) := by
      rw [moving_frame_readback hR c p₀ g hgc (hge t ht)]
      congr 1
    change readback (JetTransport.map R t (g t))=_
    rw [JetTransport.map_readback]
    have hd := TransportDuhamel.moving_frame_solution_to_duhamel R t (readback p₀)
      (g := fun s => readback (g s)) hF.continuousOn he
    simpa only [F,FreeTransport.transport_smul] using hd

/-- Any original continuous mild solution with the same C³ datum is the
readback of the constructed jet path on their common local interval. -/
theorem actual_mild_solution_has_jet_lift {R T : ℝ} (hR : 0≤R) (hT : 0≤T) (c : ℝ)
    (p₀ : Space R) (a : ℝ≥0) (ha : 0<a) (hwindow : T≤localTime R hR c p₀ a)
    (f : ℝ → FreeTransport.Distribution R) (hfc : ContinuousOn f (Icc 0 T))
    (hfe : ∀ t∈Icc 0 T,f t=FreeTransport.transport R t (readback p₀)+
      ∫ s in (0 : ℝ)..t,c • FreeTransport.transport R (t-s) (SpatialCollision.collision R hR (f s))) :
    ∃ p : ℝ → Space R, Continuous p ∧ p 0=p₀ ∧
      (∀ t,‖p t‖≤‖p₀‖+a) ∧ EqOn (fun t => readback (p t)) f (Icc 0 T) := by
  obtain ⟨p,hpc,hp0,_hpclose,hpb,_hpd,hpe⟩ := exists_mild_jet_solution R hR c p₀ a ha
  refine ⟨p,hpc,hp0,hpb,?_⟩
  exact KineticUniqueness.mild_solution_unique hR hT c (readback p₀)
    (fun t => readback (p t)) f ((readback_continuous R).comp hpc).continuousOn hfc
    (fun t ht => hpe t ⟨ht.1,ht.2.trans hwindow⟩) hfe

theorem actual_mild_solution_spatial_C3 {R T : ℝ} (hR : 0≤R) (hT : 0≤T) (c : ℝ)
    (p₀ : Space R) (a : ℝ≥0) (ha : 0<a) (hwindow : T≤localTime R hR c p₀ a)
    (f : ℝ → FreeTransport.Distribution R) (hfc : ContinuousOn f (Icc 0 T))
    (hfe : ∀ t∈Icc 0 T,f t=FreeTransport.transport R t (readback p₀)+
      ∫ s in (0 : ℝ)..t,c • FreeTransport.transport R (t-s) (SpatialCollision.collision R hR (f s))) :
    ∀ t∈Icc 0 T,ContDiff ℝ 3 (SpatialChainRule.realLift (f t)) := by
  obtain ⟨p,_hpc,_hp0,_hpb,hpf⟩ := actual_mild_solution_has_jet_lift hR hT c p₀ a ha hwindow f hfc hfe
  intro t ht
  rw [← hpf ht]
  exact SpatialJetSpace.toDistribution_contDiff (p t)

theorem exists_positive_mild_jet_solution (R : ℝ) (hR : 0≤R) (c : ℝ)
    (p₀ : Space R) (m : ℝ) (hm : 0 < m) (hp₀ : ∀ z, m ≤ readback p₀ z) :
    ∃ T : ℝ,0<T ∧ ∃ p : ℝ → Space R,Continuous p ∧ p 0=p₀ ∧
      (∀ t∈Icc 0 T,∀ z,m/2≤readback (p t) z) ∧
      (∀ t,ContDiff ℝ 3 (SpatialChainRule.realLift (readback (p t)))) ∧
      ∀ t∈Icc 0 T,readback (p t)=FreeTransport.transport R t (readback p₀)+
        ∫ s in (0 : ℝ)..t,c • FreeTransport.transport R (t-s)
          (SpatialCollision.collision R hR (readback (p s))) := by
  let a : ℝ≥0 := ⟨m/2,by positivity⟩
  have ha : 0 < a := by change 0 < m / 2; positivity
  obtain ⟨p,hpc,hp0,hpclose,_hpb,hpd,hpe⟩ := exists_mild_jet_solution R hR c p₀ a ha
  refine ⟨localTime R hR c p₀ a,localTime_pos hR c p₀ ha,p,hpc,hp0,?_,hpd,hpe⟩
  intro t _ z
  have hbound : ‖readback (p t-JetTransport.map R t p₀)‖ ≤ ‖p t-JetTransport.map R t p₀‖ :=
    SpatialJetSpace.toDistribution_norm_le (R := R) (p t-JetTransport.map R t p₀)
  have hread : ‖readback (p t-JetTransport.map R t p₀)‖ ≤ m/2 :=
    hbound.trans (hpclose t)
  have he := (ContinuousMap.norm_coe_le_norm (readback (p t-JetTransport.map R t p₀)) z).trans hread
  rw [JetTransport.readback_sub,JetTransport.map_readback] at he
  change ‖readback (p t) z-FreeTransport.transport R t (readback p₀) z‖ ≤ m/2 at he
  have hlo := (abs_le.mp (show |readback (p t) z-FreeTransport.transport R t (readback p₀) z| ≤ m/2 from he)).1
  have hi := hp₀ (FreeTransport.characteristic t z)
  change m≤FreeTransport.transport R t (readback p₀) z at hi
  linarith

/-- There is at most one compatible jet path for the same original mild
equation and initial distribution, on any common compact time interval. -/
theorem mild_jet_solution_unique {R T : ℝ} (hR : 0 ≤ R) (hT : 0 ≤ T)
    (c : ℝ) (p₀ : Space R) (p q : ℝ → Space R)
    (hp : ContinuousOn p (Icc 0 T)) (hq : ContinuousOn q (Icc 0 T))
    (he : ∀ t ∈ Icc 0 T, readback (p t) = FreeTransport.transport R t (readback p₀) +
      ∫ s in (0 : ℝ)..t, c • FreeTransport.transport R (t-s)
        (SpatialCollision.collision R hR (readback (p s))))
    (hf : ∀ t ∈ Icc 0 T, readback (q t) = FreeTransport.transport R t (readback p₀) +
      ∫ s in (0 : ℝ)..t, c • FreeTransport.transport R (t-s)
        (SpatialCollision.collision R hR (readback (q s)))) :
    EqOn p q (Icc 0 T) := by
  have h := KineticUniqueness.mild_solution_unique hR hT c (readback p₀)
    (fun t => readback (p t)) (fun t => readback (q t))
    ((readback_continuous R).comp_continuousOn hp)
    ((readback_continuous R).comp_continuousOn hq) he hf
  intro t ht
  exact readback_injective R (h ht)

/-- Entry stated directly for an actual distribution. Compatibility of all
spatial derivatives is constructed from its real-coordinate C³ lift; no
momentum differentiability and no freely assigned jet fields are requested. -/
theorem exists_positive_C3_mild_solution (R : ℝ) (hR : 0 ≤ R) (c : ℝ)
    (f₀ : FreeTransport.Distribution R)
    (hf₀ : ContDiff ℝ 3 (SpatialChainRule.realLift f₀))
    (m : ℝ) (hm : 0 < m) (hpos : ∀ z, m ≤ f₀ z) :
    ∃ T : ℝ, 0 < T ∧ ∃ p : ℝ → Space R,
      Continuous p ∧ readback (p 0) = f₀ ∧
      (∀ t ∈ Icc 0 T, ∀ z, m/2 ≤ readback (p t) z) ∧
      (∀ t, ContDiff ℝ 3 (SpatialChainRule.realLift (readback (p t)))) ∧
      ∀ t ∈ Icc 0 T, readback (p t) = FreeTransport.transport R t f₀ +
        ∫ s in (0 : ℝ)..t, c • FreeTransport.transport R (t-s)
          (SpatialCollision.collision R hR (readback (p s))) := by
  let p₀ : Space R := SpatialJetDescent.jetOfDistribution f₀ hf₀
  have hr : readback p₀ = f₀ := SpatialJetDescent.jetOfDistribution_readback f₀ hf₀
  obtain ⟨T,hT,p,hpc,hp0,hpp,hpd,hpe⟩ := exists_positive_mild_jet_solution R hR c p₀ m hm
    (by simpa only [hr] using hpos)
  refine ⟨T,hT,p,hpc,?_,hpp,hpd,?_⟩
  · rw [hp0,hr]
  · simpa only [hr] using hpe

end
end Resonance.JetLocalKinetics

#check Resonance.JetLocalKinetics.exists_moving_frame_solution
#print axioms Resonance.JetLocalKinetics.exists_moving_frame_solution
#check Resonance.JetLocalKinetics.exists_moving_frame_solution_at
#print axioms Resonance.JetLocalKinetics.exists_moving_frame_solution_at
#check Resonance.JetLocalKinetics.moving_frame_readback
#print axioms Resonance.JetLocalKinetics.moving_frame_readback
#check Resonance.JetLocalKinetics.exists_mild_jet_solution
#print axioms Resonance.JetLocalKinetics.exists_mild_jet_solution
#check Resonance.JetLocalKinetics.actual_mild_solution_has_jet_lift
#print axioms Resonance.JetLocalKinetics.actual_mild_solution_has_jet_lift
#check Resonance.JetLocalKinetics.actual_mild_solution_spatial_C3
#print axioms Resonance.JetLocalKinetics.actual_mild_solution_spatial_C3
#check Resonance.JetLocalKinetics.exists_positive_mild_jet_solution
#print axioms Resonance.JetLocalKinetics.exists_positive_mild_jet_solution
#check Resonance.JetLocalKinetics.mild_jet_solution_unique
#print axioms Resonance.JetLocalKinetics.mild_jet_solution_unique
#check Resonance.JetLocalKinetics.exists_positive_C3_mild_solution
#print axioms Resonance.JetLocalKinetics.exists_positive_C3_mild_solution
