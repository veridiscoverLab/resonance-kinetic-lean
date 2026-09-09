import Resonance.JetCollisionBounds

/-! Fixed-clock, amplitude-controlled derivative bounds for the original
kinetic solution. All derivative norms belong to its compatible jet path. -/
open Set MeasureTheory
open scoped Interval
namespace Resonance.JetAmplitudeBounds
noncomputable section
open JetCollision JetSeminorm JetCollisionBounds FreeTransport
set_option maxHeartbeats 1500000
set_option synthInstance.maxHeartbeats 50000

theorem field_seminorm (R : ℝ) (hR : 0 ≤ R) (c t : ℝ)
    (n : ℕ) (hn : n ≤ 3) (p : Space R) :
    spatialSeminorm R n hn (JetKineticField.field R hR c t p) =
      |c| * spatialSeminorm R n hn (JetCollision.collision R hR (JetTransport.map R t p)) := by
  rw [JetKineticField.field,spatialSeminorm_smul,spatialSeminorm_transport]

theorem field_first_bound {R : ℝ} (hR : 0 ≤ R) (c t : ℝ) (p : Space R) :
    spatialSeminorm R 1 (by omega) (JetKineticField.field R hR c t p) ≤
      |c| * (3*collisionConstant R*‖readback p‖^2*spatialSeminorm R 1 (by omega) p) := by
  rw [field_seminorm]
  have h := mul_le_mul_of_nonneg_left (first_seminorm_collision hR (JetTransport.map R t p))
    (abs_nonneg c)
  simpa only [JetTransport.map_readback,transport_norm,spatialSeminorm_transport] using h

theorem field_second_bound {R : ℝ} (hR : 0 ≤ R) (c t : ℝ) (p : Space R) :
    spatialSeminorm R 2 (by omega) (JetKineticField.field R hR c t p) ≤
      |c| * (6*collisionConstant R*‖readback p‖*(spatialSeminorm R 1 (by omega) p)^2 +
        3*collisionConstant R*‖readback p‖^2*spatialSeminorm R 2 (by omega) p) := by
  rw [field_seminorm]
  have h := mul_le_mul_of_nonneg_left (second_seminorm_collision hR (JetTransport.map R t p))
    (abs_nonneg c)
  simpa only [JetTransport.map_readback,transport_norm,spatialSeminorm_transport] using h

theorem field_third_bound {R : ℝ} (hR : 0 ≤ R) (c t : ℝ) (p : Space R) :
    spatialSeminorm R 3 (by omega) (JetKineticField.field R hR c t p) ≤
      |c| * (6*collisionConstant R*(spatialSeminorm R 1 (by omega) p)^3 +
        18*collisionConstant R*‖readback p‖*spatialSeminorm R 1 (by omega) p*
          spatialSeminorm R 2 (by omega) p +
        3*collisionConstant R*‖readback p‖^2*spatialSeminorm R 3 (by omega) p) := by
  rw [field_seminorm]
  have h := mul_le_mul_of_nonneg_left (third_seminorm_collision hR (JetTransport.map R t p))
    (abs_nonneg c)
  simpa only [JetTransport.map_readback,transport_norm,spatialSeminorm_transport] using h

theorem moving_frame_seminorm_gronwall {R T : ℝ} (hR : 0 ≤ R) (hT : 0 ≤ T)
    (c : ℝ) (n : ℕ) (hn : n ≤ 3) (p₀ : Space R) (g : ℝ → Space R)
    (hg : ContinuousOn g (Icc 0 T))
    (he : ∀ t ∈ Icc 0 T,g t=p₀+∫ s in (0 : ℝ)..t,JetKineticField.field R hR c s (g s))
    (A B : ℝ)
    (hb : ∀ t ∈ Ico 0 T,spatialSeminorm R n hn (JetKineticField.field R hR c t (g t)) ≤
      A*spatialSeminorm R n hn (g t)+B) :
    ∀ t ∈ Icc 0 T,spatialSeminorm R n hn (g t) ≤
      gronwallBound (spatialSeminorm R n hn p₀) A B t := by
  have hd := JetMildEquation.moving_frame_hasDerivWithinAt hR hT c p₀ g hg he
  have hg0 := he 0 ⟨le_rfl,hT⟩
  simp only [intervalIntegral.integral_same,add_zero] at hg0
  let L := orbitDerivative R n hn
  have h := norm_le_gronwallBound_of_norm_deriv_right_le
    (f := fun t => L (g t)) (f' := fun t => L (JetKineticField.field R hR c t (g t)))
    (a := 0) (b := T) (δ := spatialSeminorm R n hn p₀) (K := A) (ε := B)
    (L.continuous.comp_continuousOn hg)
    (fun t ht => L.hasFDerivAt.comp_hasDerivWithinAt t
      ((hd t (Ico_subset_Icc_self ht)).mono_of_mem_nhdsWithin (Icc_mem_nhdsGE_of_mem ht)))
    (by change ‖L (g 0)‖ ≤ _; rw [hg0]; exact le_rfl) hb
  simpa only [sub_zero] using h

def rate (R c M : ℝ) : ℝ := |c| * (3*collisionConstant R*M^2)

theorem rate_nonnegative (R c M : ℝ) : 0 ≤ rate R c M := by
  have hK := collisionConstant_nonnegative R
  unfold rate
  positivity

theorem first_gronwall {R T M : ℝ} (hR : 0 ≤ R) (hT : 0 ≤ T)
    (c : ℝ) (p₀ : Space R) (g : ℝ → Space R) (hg : ContinuousOn g (Icc 0 T))
    (he : ∀ t ∈ Icc 0 T,g t=p₀+∫ s in (0 : ℝ)..t,JetKineticField.field R hR c s (g s))
    (hamp : ∀ t ∈ Icc 0 T,‖readback (g t)‖ ≤ M) :
    ∀ t ∈ Icc 0 T,spatialSeminorm R 1 (by omega) (g t) ≤
      gronwallBound (spatialSeminorm R 1 (by omega) p₀) (rate R c M) 0 t := by
  apply moving_frame_seminorm_gronwall hR hT c 1 (by omega) p₀ g hg he
  intro t ht
  apply (field_first_bound hR c t (g t)).trans
  have hm := hamp t (Ico_subset_Icc_self ht)
  have hK := collisionConstant_nonnegative R
  have hJ := spatialSeminorm_nonnegative R 1 (by omega) (g t)
  dsimp only [rate]
  rw [add_zero]
  calc
    _ ≤ |c| * (3*collisionConstant R*M^2*spatialSeminorm R 1 (by omega) (g t)) := by gcongr
    _ = _ := by ring

def firstBudget (R c M T : ℝ) (p₀ : Space R) : ℝ :=
  gronwallBound (spatialSeminorm R 1 (by omega) p₀) (rate R c M) 0 T

def secondSource (R c M T : ℝ) (p₀ : Space R) : ℝ :=
  |c| * (6*collisionConstant R*M*(firstBudget R c M T p₀)^2)

def secondBudget (R c M T : ℝ) (p₀ : Space R) : ℝ :=
  gronwallBound (spatialSeminorm R 2 (by omega) p₀) (rate R c M)
    (secondSource R c M T p₀) T

def thirdSource (R c M T : ℝ) (p₀ : Space R) : ℝ :=
  |c| * (6*collisionConstant R*(firstBudget R c M T p₀)^3 +
    18*collisionConstant R*M*firstBudget R c M T p₀*secondBudget R c M T p₀)

def thirdBudget (R c M T : ℝ) (p₀ : Space R) : ℝ :=
  gronwallBound (spatialSeminorm R 3 (by omega) p₀) (rate R c M)
    (thirdSource R c M T p₀) T

theorem gronwall_nonnegative {δ A B t : ℝ} (hδ : 0 ≤ δ) (hA : 0 ≤ A)
    (hB : 0 ≤ B) (ht : 0 ≤ t) : 0 ≤ gronwallBound δ A B t := by
  have h := gronwallBound_mono hδ hB hA ht
  rw [gronwallBound_x0] at h
  exact hδ.trans h

theorem budgets_nonnegative {R c M T : ℝ} (hM : 0 ≤ M) (hT : 0 ≤ T) (p₀ : Space R) :
    0 ≤ firstBudget R c M T p₀ ∧ 0 ≤ secondSource R c M T p₀ ∧
    0 ≤ secondBudget R c M T p₀ ∧ 0 ≤ thirdSource R c M T p₀ ∧
    0 ≤ thirdBudget R c M T p₀ := by
  have hK := collisionConstant_nonnegative R
  have hA := rate_nonnegative R c M
  have h1 : 0 ≤ firstBudget R c M T p₀ :=
    gronwall_nonnegative (spatialSeminorm_nonnegative ..) hA le_rfl hT
  have hS2 : 0 ≤ secondSource R c M T p₀ := by unfold secondSource; positivity
  have h2 : 0 ≤ secondBudget R c M T p₀ :=
    gronwall_nonnegative (spatialSeminorm_nonnegative ..) hA hS2 hT
  have hS3 : 0 ≤ thirdSource R c M T p₀ := by unfold thirdSource; positivity
  have h3 : 0 ≤ thirdBudget R c M T p₀ :=
    gronwall_nonnegative (spatialSeminorm_nonnegative ..) hA hS3 hT
  exact ⟨h1,hS2,h2,hS3,h3⟩

theorem first_uniform {R T M : ℝ} (hR : 0 ≤ R) (hT : 0 ≤ T)
    (c : ℝ) (p₀ : Space R) (g : ℝ → Space R) (hg : ContinuousOn g (Icc 0 T))
    (he : ∀ t ∈ Icc 0 T,g t=p₀+∫ s in (0 : ℝ)..t,JetKineticField.field R hR c s (g s))
    (hamp : ∀ t ∈ Icc 0 T,‖readback (g t)‖ ≤ M) :
    ∀ t ∈ Icc 0 T,spatialSeminorm R 1 (by omega) (g t) ≤ firstBudget R c M T p₀ := by
  intro t ht
  apply (first_gronwall hR hT c p₀ g hg he hamp t ht).trans
  exact gronwallBound_mono (spatialSeminorm_nonnegative ..) le_rfl (rate_nonnegative ..) ht.2

theorem second_uniform {R T M : ℝ} (hR : 0 ≤ R) (hT : 0 ≤ T) (hM : 0 ≤ M)
    (c : ℝ) (p₀ : Space R) (g : ℝ → Space R) (hg : ContinuousOn g (Icc 0 T))
    (he : ∀ t ∈ Icc 0 T,g t=p₀+∫ s in (0 : ℝ)..t,JetKineticField.field R hR c s (g s))
    (hamp : ∀ t ∈ Icc 0 T,‖readback (g t)‖ ≤ M) :
    ∀ t ∈ Icc 0 T,spatialSeminorm R 2 (by omega) (g t) ≤ secondBudget R c M T p₀ := by
  have h1 := first_uniform hR hT c p₀ g hg he hamp
  have hn := budgets_nonnegative (R := R) (c := c) hM hT p₀
  have hK := collisionConstant_nonnegative R
  have hb : ∀ t ∈ Ico 0 T,
      spatialSeminorm R 2 (by omega) (JetKineticField.field R hR c t (g t)) ≤
        rate R c M*spatialSeminorm R 2 (by omega) (g t)+secondSource R c M T p₀ := by
    intro t ht
    apply (field_second_bound hR c t (g t)).trans
    have hm := hamp t (Ico_subset_Icc_self ht)
    have hj := h1 t (Ico_subset_Icc_self ht)
    have hj0 := spatialSeminorm_nonnegative R 1 (by omega) (g t)
    have hj2 := spatialSeminorm_nonnegative R 2 (by omega) (g t)
    calc
      _ ≤ |c| * (6*collisionConstant R*M*(firstBudget R c M T p₀)^2 +
          3*collisionConstant R*M^2*spatialSeminorm R 2 (by omega) (g t)) := by gcongr
      _ = _ := by unfold rate secondSource; ring
  have h := moving_frame_seminorm_gronwall hR hT c 2 (by omega) p₀ g hg he
    (rate R c M) (secondSource R c M T p₀) hb
  intro t ht
  exact (h t ht).trans (gronwallBound_mono (spatialSeminorm_nonnegative ..)
    hn.2.1 (rate_nonnegative ..) ht.2)

theorem third_uniform {R T M : ℝ} (hR : 0 ≤ R) (hT : 0 ≤ T) (hM : 0 ≤ M)
    (c : ℝ) (p₀ : Space R) (g : ℝ → Space R) (hg : ContinuousOn g (Icc 0 T))
    (he : ∀ t ∈ Icc 0 T,g t=p₀+∫ s in (0 : ℝ)..t,JetKineticField.field R hR c s (g s))
    (hamp : ∀ t ∈ Icc 0 T,‖readback (g t)‖ ≤ M) :
    ∀ t ∈ Icc 0 T,spatialSeminorm R 3 (by omega) (g t) ≤ thirdBudget R c M T p₀ := by
  have h1 := first_uniform hR hT c p₀ g hg he hamp
  have h2 := second_uniform hR hT hM c p₀ g hg he hamp
  have hn := budgets_nonnegative (R := R) (c := c) hM hT p₀
  have hK := collisionConstant_nonnegative R
  have hB1 := hn.1
  have hB2 := hn.2.2.1
  have hb : ∀ t ∈ Ico 0 T,
      spatialSeminorm R 3 (by omega) (JetKineticField.field R hR c t (g t)) ≤
        rate R c M*spatialSeminorm R 3 (by omega) (g t)+thirdSource R c M T p₀ := by
    intro t ht
    apply (field_third_bound hR c t (g t)).trans
    have hm := hamp t (Ico_subset_Icc_self ht)
    have hj := h1 t (Ico_subset_Icc_self ht)
    have hj2 := h2 t (Ico_subset_Icc_self ht)
    have hj0 := spatialSeminorm_nonnegative R 1 (by omega) (g t)
    have hj20 := spatialSeminorm_nonnegative R 2 (by omega) (g t)
    have hj30 := spatialSeminorm_nonnegative R 3 (by omega) (g t)
    calc
      _ ≤ |c| * (6*collisionConstant R*(firstBudget R c M T p₀)^3 +
          18*collisionConstant R*M*firstBudget R c M T p₀*secondBudget R c M T p₀ +
          3*collisionConstant R*M^2*spatialSeminorm R 3 (by omega) (g t)) := by gcongr
      _ = _ := by unfold rate thirdSource; ring
  have h := moving_frame_seminorm_gronwall hR hT c 3 (by omega) p₀ g hg he
    (rate R c M) (thirdSource R c M T p₀) hb
  intro t ht
  exact (h t ht).trans (gronwallBound_mono (spatialSeminorm_nonnegative ..)
    hn.2.2.2.1 (rate_nonnegative ..) ht.2)

def jetBudget (R c M T : ℝ) (p₀ : Space R) : ℝ :=
  M+firstBudget R c M T p₀+secondBudget R c M T p₀+thirdBudget R c M T p₀

theorem norm_bound_of_amplitude {R T M : ℝ} (hR : 0 ≤ R) (hT : 0 ≤ T) (hM : 0 ≤ M)
    (c : ℝ) (p₀ : Space R) (g : ℝ → Space R) (hg : ContinuousOn g (Icc 0 T))
    (he : ∀ t ∈ Icc 0 T,g t=p₀+∫ s in (0 : ℝ)..t,JetKineticField.field R hR c s (g s))
    (hamp : ∀ t ∈ Icc 0 T,‖readback (g t)‖ ≤ M) :
    ∀ t ∈ Icc 0 T,‖g t‖ ≤ jetBudget R c M T p₀ := by
  intro t ht
  have h1 := first_uniform hR hT c p₀ g hg he hamp t ht
  have h2 := second_uniform hR hT hM c p₀ g hg he hamp t ht
  have h3 := third_uniform hR hT hM c p₀ g hg he hamp t ht
  have h0 := hamp t ht
  have hn := norm_le_sum_spatialSeminorm R (g t)
  simp only [Fin.sum_univ_four] at hn
  change ‖g t‖ ≤ spatialSeminorm R 0 (by omega) (g t)+spatialSeminorm R 1 (by omega) (g t)+
    spatialSeminorm R 2 (by omega) (g t)+spatialSeminorm R 3 (by omega) (g t) at hn
  rw [spatialSeminorm_zero] at hn
  unfold jetBudget
  linarith

def toFrame (R : ℝ) (p : ℝ → Space R) (t : ℝ) : Space R :=
  JetTransport.map R (-t) (p t)

theorem toFrame_continuousOn {R : ℝ} {p : ℝ → Space R} {s : Set ℝ}
    (hp : ContinuousOn p s) : ContinuousOn (toFrame R p) s :=
  (JetTransport.map_joint_continuous R).comp_continuousOn
    (continuous_neg.continuousOn.prodMk hp)

theorem toFrame_seminorm (R : ℝ) (p : ℝ → Space R) (t : ℝ) (n : ℕ) (hn : n ≤ 3) :
    spatialSeminorm R n hn (toFrame R p t)=spatialSeminorm R n hn (p t) :=
  spatialSeminorm_transport R (-t) n hn (p t)

theorem actual_mild_to_moving_frame {R T : ℝ} (hR : 0 ≤ R) (c : ℝ)
    (p₀ : Space R) (p : ℝ → Space R) (hp : ContinuousOn p (Icc 0 T))
    (he : ∀ t ∈ Icc 0 T,readback (p t)=transport R t (readback p₀)+
      ∫ s in (0 : ℝ)..t,c • transport R (t-s)
        (SpatialCollision.collision R hR (readback (p s)))) :
    ∀ t ∈ Icc 0 T,toFrame R p t=p₀+
      ∫ s in (0 : ℝ)..t,JetKineticField.field R hR c s (toFrame R p s) := by
  have hg := toFrame_continuousOn hp
  have hread := (readback_continuous R).comp_continuousOn hp
  have hh := KineticUniqueness.mild_to_moving_frame hR c (readback p₀)
    (fun t => readback (p t)) hread he
  intro t ht
  have hi : IntervalIntegrable
      (fun s => JetKineticField.field R hR c s (toFrame R p s)) volume 0 t :=
    (((JetKineticField.field_joint_continuous R hR c).comp_continuousOn
      (continuous_id.continuousOn.prodMk hg)).mono
        (uIcc_subset_Icc ⟨le_rfl,ht.1.trans ht.2⟩ ht)).intervalIntegrable
  apply readback_injective R
  rw [readback_add]
  change readback (toFrame R p t)=readback p₀+
    JetLocalKinetics.readbackOperator R
      (∫ s in (0 : ℝ)..t,JetKineticField.field R hR c s (toFrame R p s))
  rw [← (JetLocalKinetics.readbackOperator R).intervalIntegral_comp_comm hi]
  change readback (toFrame R p t)=readback p₀+
    ∫ s in (0 : ℝ)..t,readback (JetKineticField.field R hR c s (toFrame R p s))
  simpa only [JetKineticField.field_readback,toFrame,JetTransport.map_readback,
    KineticUniqueness.toFrame] using hh t ht

/-- The amplitude budget controls the compatible C³ norm of the same original
mild solution, not merely an independently postulated tensor evolution. -/
theorem actual_mild_norm_bound {R T M : ℝ} (hR : 0 ≤ R) (hT : 0 ≤ T) (hM : 0 ≤ M)
    (c : ℝ) (p₀ : Space R) (p : ℝ → Space R) (hp : ContinuousOn p (Icc 0 T))
    (he : ∀ t ∈ Icc 0 T,readback (p t)=transport R t (readback p₀)+
      ∫ s in (0 : ℝ)..t,c • transport R (t-s)
        (SpatialCollision.collision R hR (readback (p s))))
    (hamp : ∀ t ∈ Icc 0 T,‖readback (p t)‖ ≤ M) :
    ∀ t ∈ Icc 0 T,‖p t‖ ≤ jetBudget R c M T p₀ := by
  have hg := toFrame_continuousOn hp
  have hge := actual_mild_to_moving_frame hR c p₀ p hp he
  have hga : ∀ t ∈ Icc 0 T,‖readback (toFrame R p t)‖ ≤ M := by
    intro t ht
    simpa only [toFrame,JetTransport.map_readback,transport_norm] using hamp t ht
  have h := norm_bound_of_amplitude hR hT hM c p₀ (toFrame R p) hg hge hga
  simpa only [toFrame,JetTransport.map_norm] using h

end
end Resonance.JetAmplitudeBounds

#check Resonance.JetAmplitudeBounds.field_seminorm
#check Resonance.JetAmplitudeBounds.field_first_bound
#check Resonance.JetAmplitudeBounds.field_second_bound
#check Resonance.JetAmplitudeBounds.field_third_bound
#check Resonance.JetAmplitudeBounds.moving_frame_seminorm_gronwall
#check Resonance.JetAmplitudeBounds.rate_nonnegative
#check Resonance.JetAmplitudeBounds.first_gronwall
#check Resonance.JetAmplitudeBounds.gronwall_nonnegative
#check Resonance.JetAmplitudeBounds.budgets_nonnegative
#check Resonance.JetAmplitudeBounds.first_uniform
#check Resonance.JetAmplitudeBounds.second_uniform
#check Resonance.JetAmplitudeBounds.third_uniform
#check Resonance.JetAmplitudeBounds.norm_bound_of_amplitude
#check Resonance.JetAmplitudeBounds.toFrame_continuousOn
#check Resonance.JetAmplitudeBounds.toFrame_seminorm
#check Resonance.JetAmplitudeBounds.actual_mild_to_moving_frame
#check Resonance.JetAmplitudeBounds.actual_mild_norm_bound
#print axioms Resonance.JetAmplitudeBounds.field_seminorm
#print axioms Resonance.JetAmplitudeBounds.field_first_bound
#print axioms Resonance.JetAmplitudeBounds.field_second_bound
#print axioms Resonance.JetAmplitudeBounds.field_third_bound
#print axioms Resonance.JetAmplitudeBounds.moving_frame_seminorm_gronwall
#print axioms Resonance.JetAmplitudeBounds.rate_nonnegative
#print axioms Resonance.JetAmplitudeBounds.first_gronwall
#print axioms Resonance.JetAmplitudeBounds.gronwall_nonnegative
#print axioms Resonance.JetAmplitudeBounds.budgets_nonnegative
#print axioms Resonance.JetAmplitudeBounds.first_uniform
#print axioms Resonance.JetAmplitudeBounds.second_uniform
#print axioms Resonance.JetAmplitudeBounds.third_uniform
#print axioms Resonance.JetAmplitudeBounds.norm_bound_of_amplitude
#print axioms Resonance.JetAmplitudeBounds.toFrame_continuousOn
#print axioms Resonance.JetAmplitudeBounds.toFrame_seminorm
#print axioms Resonance.JetAmplitudeBounds.actual_mild_to_moving_frame
#print axioms Resonance.JetAmplitudeBounds.actual_mild_norm_bound
