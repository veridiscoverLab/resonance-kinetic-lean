import Resonance.JetContinuation

/-! The finite endpoint of an amplitude-bounded actual C³ path is recovered
from its complete Banach integral, then continued on the original clock. -/
open Set MeasureTheory
open scoped Interval
namespace Resonance.JetOpenContinuation
noncomputable section
open JetCollision JetSeminorm JetAmplitudeBounds JetContinuation JetKineticField FreeTransport
set_option maxHeartbeats 1500000
set_option synthInstance.maxHeartbeats 50000

theorem gronwall_source_mono {δ A B C t : ℝ} (hA : 0 ≤ A) (ht : 0 ≤ t) (hBC : B ≤ C) :
    gronwallBound δ A B t ≤ gronwallBound δ A C t := by
  by_cases ha : A=0
  · simp only [gronwallBound,if_pos ha]
    gcongr
  · have ha0 : 0 < A := lt_of_le_of_ne hA (Ne.symm ha)
    have he : 0 ≤ Real.exp (A*t)-1 := sub_nonneg.mpr (Real.one_le_exp_iff.mpr (mul_nonneg hA ht))
    simp only [gronwallBound,if_neg ha]
    gcongr

theorem budgets_mono_time {R c M S T : ℝ} (hM : 0 ≤ M) (hS : 0 ≤ S) (hST : S ≤ T)
    (p₀ : Space R) :
    firstBudget R c M S p₀ ≤ firstBudget R c M T p₀ ∧
    secondSource R c M S p₀ ≤ secondSource R c M T p₀ ∧
    secondBudget R c M S p₀ ≤ secondBudget R c M T p₀ ∧
    thirdSource R c M S p₀ ≤ thirdSource R c M T p₀ ∧
    thirdBudget R c M S p₀ ≤ thirdBudget R c M T p₀ := by
  have hnS := budgets_nonnegative (R := R) (c := c) hM hS p₀
  have hnT := budgets_nonnegative (R := R) (c := c) hM (hS.trans hST) p₀
  have hK := JetCollisionBounds.collisionConstant_nonnegative R
  have hA := rate_nonnegative R c M
  have h1 : firstBudget R c M S p₀ ≤ firstBudget R c M T p₀ :=
    gronwallBound_mono (spatialSeminorm_nonnegative ..) le_rfl hA hST
  have hS2 : secondSource R c M S p₀ ≤ secondSource R c M T p₀ := by
    unfold secondSource
    have hbS := hnS.1
    gcongr
  have h2 : secondBudget R c M S p₀ ≤ secondBudget R c M T p₀ :=
    (gronwall_source_mono hA hS hS2).trans
      (gronwallBound_mono (spatialSeminorm_nonnegative ..) hnT.2.1 hA hST)
  have hS3 : thirdSource R c M S p₀ ≤ thirdSource R c M T p₀ := by
    unfold thirdSource
    have hbS1 := hnS.1
    have hbS2 := hnS.2.2.1
    have hbT1 := hnT.1
    have hbT2 := hnT.2.2.1
    gcongr
  have h3 : thirdBudget R c M S p₀ ≤ thirdBudget R c M T p₀ :=
    (gronwall_source_mono hA hS hS3).trans
      (gronwallBound_mono (spatialSeminorm_nonnegative ..) hnT.2.2.2.1 hA hST)
  exact ⟨h1,hS2,h2,hS3,h3⟩

theorem jetBudget_mono_time {R c M S T : ℝ} (hM : 0 ≤ M) (hS : 0 ≤ S) (hST : S ≤ T)
    (p₀ : Space R) : jetBudget R c M S p₀ ≤ jetBudget R c M T p₀ := by
  have h := budgets_mono_time (R := R) (c := c) hM hS hST p₀
  unfold jetBudget
  linarith [h.1,h.2.2.1,h.2.2.2.2]

theorem open_moving_frame_norm_bound {R T M : ℝ} (hR : 0 ≤ R) (hM : 0 ≤ M)
    (c : ℝ) (p₀ : Space R) (g : ℝ → Space R) (hg : ContinuousOn g (Ico 0 T))
    (he : ∀ t ∈ Ico 0 T,g t=p₀+∫ s in (0 : ℝ)..t,field R hR c s (g s))
    (hamp : ∀ t ∈ Ico 0 T,‖readback (g t)‖ ≤ M) :
    ∀ t ∈ Ico 0 T,‖g t‖ ≤ jetBudget R c M T p₀ := by
  intro t ht
  have hs : Icc (0 : ℝ) t ⊆ Ico 0 T := fun s hs => ⟨hs.1,hs.2.trans_lt ht.2⟩
  have h := norm_bound_of_amplitude hR ht.1 hM c p₀ g (hg.mono hs)
    (fun s hs' => he s (hs hs')) (fun s hs' => hamp s (hs hs')) t ⟨ht.1,le_rfl⟩
  exact h.trans (jetBudget_mono_time hM ht.1 ht.2.le p₀)

theorem bounded_continuous_Ico_integrable {E : Type*} [NormedAddCommGroup E]
    {a b C : ℝ} {F : ℝ → E} (hF : ContinuousOn F (Ico a b))
    (hb : ∀ t ∈ Ico a b,‖F t‖ ≤ C) : IntegrableOn F (Icc a b) := by
  have hi : IntegrableOn F (Ico a b) :=
    (integrable_const C : Integrable (fun _ : ℝ => C) (volume.restrict (Ico a b))).mono'
      (hF.aestronglyMeasurable measurableSet_Ico)
      ((ae_restrict_iff' measurableSet_Ico).mpr (Filter.Eventually.of_forall hb))
  exact (integrableOn_Icc_iff_integrableOn_Ico (f := F) (μ := volume) (a := a) (b := b)).mpr hi

theorem continuous_field_along {E F : Type*} [TopologicalSpace E] [TopologicalSpace F]
    {s : Set ℝ} {H : ℝ → E → F} (hH : Continuous (Function.uncurry H))
    {g : ℝ → E} (hg : ContinuousOn g s) : ContinuousOn (fun t => H t (g t)) s :=
  hH.comp_continuousOn (continuous_id.continuousOn.prodMk hg)

theorem open_field_integrable {R T M : ℝ} (hR : 0 ≤ R) (hM : 0 ≤ M)
    (c : ℝ) (p₀ : Space R) (g : ℝ → Space R) (hg : ContinuousOn g (Ico 0 T))
    (he : ∀ t ∈ Ico 0 T,g t=p₀+∫ s in (0 : ℝ)..t,field R hR c s (g s))
    (hamp : ∀ t ∈ Ico 0 T,‖readback (g t)‖ ≤ M) :
    IntegrableOn (fun t => field R hR c t (g t)) (Icc 0 T) := by
  have hb := open_moving_frame_norm_bound (R := R) hR hM c p₀ g hg he hamp
  let B := |c| * ‖JetCollision.trilinear R hR‖*(jetBudget R c M T p₀)^3
  have hB : ∀ t ∈ Ico 0 T,‖field R hR c t (g t)‖ ≤ B := by
    intro t ht
    apply (field_norm_le R hR c t (g t)).trans
    exact mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (norm_nonneg (g t)) (hb t ht) 3)
      (mul_nonneg (abs_nonneg c) (norm_nonneg (JetCollision.trilinear R hR)))
  have hc : ContinuousOn (fun t => field R hR c t (g t)) (Ico 0 T) :=
    continuous_field_along (E := Space R) (F := Space R) (H := field R hR c)
      (field_joint_continuous R hR c) hg
  exact bounded_continuous_Ico_integrable (E := Space R) hc hB

/-- The endpoint is the original full time primitive. Its existence is
derived from amplitude bounds, not postulated as a terminal jet. -/
theorem moving_frame_endpoint {R T M : ℝ} (hR : 0 ≤ R) (hT : 0 < T) (hM : 0 ≤ M)
    (c : ℝ) (p₀ : Space R) (g : ℝ → Space R) (hg : ContinuousOn g (Ico 0 T))
    (he : ∀ t ∈ Ico 0 T,g t=p₀+∫ s in (0 : ℝ)..t,field R hR c s (g s))
    (hamp : ∀ t ∈ Ico 0 T,‖readback (g t)‖ ≤ M) :
    ∃ v : ℝ → Space R,ContinuousOn v (Icc 0 T) ∧ EqOn v g (Ico 0 T) ∧
      ∀ t ∈ Icc 0 T,v t=p₀+∫ s in (0 : ℝ)..t,field R hR c s (v s) := by
  have hi := open_field_integrable hR hM c p₀ g hg he hamp
  let v : ℝ → Space R := fun t => p₀+∫ s in (0 : ℝ)..t,field R hR c s (g s)
  have hv : ContinuousOn v (Icc 0 T) := by
    have h := (continuousOn_const : ContinuousOn (fun _ : ℝ => p₀) (uIcc 0 T)).add
      (intervalIntegral.continuousOn_primitive_interval
      (show IntegrableOn (fun s => field R hR c s (g s)) (uIcc 0 T) from by
        rwa [uIcc_of_le hT.le]))
    simpa only [uIcc_of_le hT.le] using h
  have heq : EqOn v g (Ico 0 T) := fun t ht => (he t ht).symm
  refine ⟨v,hv,heq,?_⟩
  intro t ht
  change p₀+(∫ s in (0 : ℝ)..t,field R hR c s (g s))=
    p₀+∫ s in (0 : ℝ)..t,field R hR c s (v s)
  congr 1
  apply intervalIntegral.integral_congr_ae
  have ha : ∀ᵐ s : ℝ ∂volume,s ≠ T := by rw [ae_iff]; simp
  filter_upwards [ha] with s hs hst
  rw [uIoc_of_le ht.1] at hst
  have hsT : s < T := lt_of_le_of_ne (hst.2.trans ht.2) hs
  change field R hR c s (g s)=field R hR c s (v s)
  rw [heq ⟨hst.1.le,hsT⟩]

theorem moving_frame_continuation {R T M : ℝ} (hR : 0 ≤ R) (hT : 0 < T) (hM : 0 ≤ M)
    (c : ℝ) (p₀ : Space R) (g : ℝ → Space R) (hg : ContinuousOn g (Ico 0 T))
    (he : ∀ t ∈ Ico 0 T,g t=p₀+∫ s in (0 : ℝ)..t,field R hR c s (g s))
    (hamp : ∀ t ∈ Ico 0 T,‖readback (g t)‖ ≤ M) :
    ∃ U : ℝ,T < U ∧ ∃ v : ℝ → Space R,ContinuousOn v (Icc 0 U) ∧
      EqOn v g (Ico 0 T) ∧
      ∀ t ∈ Icc 0 U,v t=p₀+∫ s in (0 : ℝ)..t,field R hR c s (v s) := by
  obtain ⟨v,hv,hvg,hve⟩ := moving_frame_endpoint hR hT hM c p₀ g hg he hamp
  obtain ⟨q,hq,hqv,hqe⟩ := moving_frame_extension hR hT.le (norm_nonneg (v T)) c p₀ v
    hv hve (le_refl ‖v T‖)
  refine ⟨T+extensionTime R hR c ‖v T‖,
    lt_add_of_pos_right T (extensionTime_pos hR c (norm_nonneg (v T))),q,hq,?_,hqe⟩
  intro t ht
  exact (hqv (Ico_subset_Icc_self ht)).trans (hvg ht)

/-- Amplitude-only finite-time continuation of the same original C³ mild
solution. No endpoint value, derivative bound, or extra jet field is assumed. -/
theorem actual_amplitude_only_continuation {R T M : ℝ} (hR : 0 ≤ R) (hT : 0 < T)
    (hM : 0 ≤ M) (c : ℝ) (p₀ : Space R) (p : ℝ → Space R)
    (hp : ContinuousOn p (Ico 0 T))
    (he : ∀ t ∈ Ico 0 T,readback (p t)=transport R t (readback p₀)+
      ∫ s in (0 : ℝ)..t,c • transport R (t-s)
        (SpatialCollision.collision R hR (readback (p s))))
    (hamp : ∀ t ∈ Ico 0 T,‖readback (p t)‖ ≤ M) :
    ∃ U : ℝ,T < U ∧ ∃ q : ℝ → Space R,ContinuousOn q (Icc 0 U) ∧
      EqOn q p (Ico 0 T) ∧
      ∀ t ∈ Icc 0 U,readback (q t)=transport R t (readback p₀)+
        ∫ s in (0 : ℝ)..t,c • transport R (t-s)
          (SpatialCollision.collision R hR (readback (q s))) := by
  have hg := toFrame_continuousOn hp
  have hge : ∀ t ∈ Ico 0 T,toFrame R p t=p₀+
      ∫ s in (0 : ℝ)..t,field R hR c s (toFrame R p s) := by
    intro t ht
    have hs : Icc (0 : ℝ) t ⊆ Ico 0 T := fun s hs => ⟨hs.1,hs.2.trans_lt ht.2⟩
    exact actual_mild_to_moving_frame hR c p₀ p (hp.mono hs)
      (fun s hs' => he s (hs hs')) t ⟨ht.1,le_rfl⟩
  have hga : ∀ t ∈ Ico 0 T,‖readback (toFrame R p t)‖ ≤ M := by
    intro t ht
    simpa only [toFrame,JetTransport.map_readback,transport_norm] using hamp t ht
  obtain ⟨U,hU,v,hv,hvp,hve⟩ := moving_frame_continuation hR hT hM c p₀ (toFrame R p)
    hg hge hga
  refine ⟨U,hU,fun t => JetTransport.map R t (v t),
    (JetTransport.map_joint_continuous R).comp_continuousOn
      (continuous_id.continuousOn.prodMk hv),?_,?_⟩
  · intro t ht
    change JetTransport.map R t (v t)=p t
    rw [hvp ht]
    change JetTransport.map R t (JetTransport.map R (-t) (p t))=p t
    rw [JetTransport.map_add_time,add_neg_cancel,JetTransport.map_zero_time]
  · exact moving_frame_to_actual_mild hR c p₀ v hv hve

end
end Resonance.JetOpenContinuation

#check Resonance.JetOpenContinuation.gronwall_source_mono
#check Resonance.JetOpenContinuation.budgets_mono_time
#check Resonance.JetOpenContinuation.jetBudget_mono_time
#check Resonance.JetOpenContinuation.open_moving_frame_norm_bound
#check Resonance.JetOpenContinuation.bounded_continuous_Ico_integrable
#check Resonance.JetOpenContinuation.continuous_field_along
#check Resonance.JetOpenContinuation.open_field_integrable
#check Resonance.JetOpenContinuation.moving_frame_endpoint
#check Resonance.JetOpenContinuation.moving_frame_continuation
#check Resonance.JetOpenContinuation.actual_amplitude_only_continuation
#print axioms Resonance.JetOpenContinuation.gronwall_source_mono
#print axioms Resonance.JetOpenContinuation.budgets_mono_time
#print axioms Resonance.JetOpenContinuation.jetBudget_mono_time
#print axioms Resonance.JetOpenContinuation.open_moving_frame_norm_bound
#print axioms Resonance.JetOpenContinuation.bounded_continuous_Ico_integrable
#print axioms Resonance.JetOpenContinuation.continuous_field_along
#print axioms Resonance.JetOpenContinuation.open_field_integrable
#print axioms Resonance.JetOpenContinuation.moving_frame_endpoint
#print axioms Resonance.JetOpenContinuation.moving_frame_continuation
#print axioms Resonance.JetOpenContinuation.actual_amplitude_only_continuation
