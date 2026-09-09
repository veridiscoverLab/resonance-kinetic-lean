import Resonance.LocalKinetics
import Mathlib.Analysis.ODE.Gronwall

/-! Actual uniqueness in the class of continuous mild solutions. Uniform
amplitude bounds needed by the comparison theorem are obtained from compact
time intervals, not postulated as an extra hypothesis on the collision kernel. -/
open Set Metric MeasureTheory
open scoped NNReal Interval

namespace Resonance.KineticUniqueness
noncomputable section
open FreeTransport SpatialCollision KineticField TransportDuhamel

def toFrame {R : ℝ} (f : ℝ → Distribution R) (t : ℝ) : Distribution R :=
  transport R (-t) (f t)

theorem fromFrame_toFrame {R : ℝ} (f : ℝ → Distribution R) (t : ℝ) :
    transport R t (toFrame f t) = f t := by
  unfold toFrame
  rw [transport_add_time, add_neg_cancel, transport_zero]

theorem toFrame_continuousOn {R : ℝ} {f : ℝ → Distribution R} {s : Set ℝ}
    (hf : ContinuousOn f s) : ContinuousOn (toFrame f) s :=
  (transport_joint_continuous R).comp_continuousOn (continuous_neg.continuousOn.prodMk hf)

theorem mild_to_moving_frame {R T : ℝ} (hR : 0 ≤ R) (c : ℝ)
    (f₀ : Distribution R) (f : ℝ → Distribution R) (hf : ContinuousOn f (Icc 0 T))
    (he : ∀ t ∈ Icc 0 T, f t = transport R t f₀ +
      ∫ s in (0 : ℝ)..t, c • transport R (t-s) (collision R hR (f s))) :
    ∀ t ∈ Icc 0 T, toFrame f t = f₀ +
      ∫ s in (0 : ℝ)..t, field R hR c s (toFrame f s) := by
  intro t ht
  let F : ℝ → Distribution R := fun s => c • collision R hR (f s)
  have hF : ContinuousOn F (uIcc 0 t) :=
    (((collision_continuous hR).comp_continuousOn hf).const_smul c).mono
      (uIcc_subset_Icc ⟨le_rfl, ht.1.trans ht.2⟩ ht)
  have he' : f t = transport R t (f₀ +
      ∫ s in (0 : ℝ)..t, transport R (-s) (F s)) := by
    rw [duhamel_identity R t f₀ hF]
    exact he t ht
  unfold toFrame at ⊢
  rw [he', transport_add_time, neg_add_cancel, transport_zero]
  congr 1
  apply intervalIntegral.integral_congr
  intro s _
  change transport R (-s) (c • collision R hR (f s)) =
    field R hR c s (toFrame f s)
  rw [field, fromFrame_toFrame, transport_smul]

theorem moving_frame_hasDerivWithinAt {R T : ℝ} (hR : 0 ≤ R) (hT : 0 ≤ T)
    (c : ℝ) (f₀ : Distribution R) (g : ℝ → Distribution R)
    (hg : ContinuousOn g (Icc 0 T))
    (he : ∀ t ∈ Icc 0 T, g t = f₀ +
      ∫ s in (0 : ℝ)..t, field R hR c s (g s)) :
    ∀ t ∈ Icc 0 T, HasDerivWithinAt g (field R hR c t (g t)) (Icc 0 T) t := by
  intro t ht
  apply (ODE.hasDerivWithinAt_picard_Icc (⟨le_rfl,hT⟩ : 0 ∈ Icc 0 T)
    (u := Set.univ) (field_joint_continuous R hR c).continuousOn hg
    (fun _ _ => Set.mem_univ _) f₀ ht).congr_of_mem _ ht
  intro s hs
  exact he s hs

theorem moving_frame_unique {R T : ℝ} (hR : 0 ≤ R) (hT : 0 ≤ T)
    (c : ℝ) (f₀ : Distribution R) (g h : ℝ → Distribution R)
    (hgc : ContinuousOn g (Icc 0 T)) (hhc : ContinuousOn h (Icc 0 T))
    (hge : ∀ t ∈ Icc 0 T, g t = f₀ +
      ∫ s in (0 : ℝ)..t, field R hR c s (g s))
    (hhe : ∀ t ∈ Icc 0 T, h t = f₀ +
      ∫ s in (0 : ℝ)..t, field R hR c s (h s)) : EqOn g h (Icc 0 T) := by
  obtain ⟨Cg,hCg⟩ := isCompact_Icc.exists_bound_of_continuousOn hgc
  obtain ⟨Ch,hCh⟩ := isCompact_Icc.exists_bound_of_continuousOn hhc
  let M : ℝ≥0 := ⟨max 0 (max Cg Ch), le_max_left _ _⟩
  have hgb : ∀ t ∈ Icc 0 T, g t ∈ closedBall (0 : Distribution R) (M : ℝ) := by
    intro t ht
    rw [mem_closedBall, dist_zero_right]
    exact (hCg t ht).trans ((le_max_left Cg Ch).trans (le_max_right 0 _))
  have hhb : ∀ t ∈ Icc 0 T, h t ∈ closedBall (0 : Distribution R) (M : ℝ) := by
    intro t ht
    rw [mem_closedBall, dist_zero_right]
    exact (hCh t ht).trans ((le_max_right Cg Ch).trans (le_max_right 0 _))
  have hgd := moving_frame_hasDerivWithinAt hR hT c f₀ g hgc hge
  have hhd := moving_frame_hasDerivWithinAt hR hT c f₀ h hhc hhe
  apply ODE_solution_unique_of_mem_Icc_right
    (fun t _ => field_lipschitz_ball R hR c t 0 M) hgc
    (fun t ht => (hgd t (Ico_subset_Icc_self ht)).mono_of_mem_nhdsWithin
      (Icc_mem_nhdsGE_of_mem ht))
    (fun t ht => hgb t (Ico_subset_Icc_self ht)) hhc
    (fun t ht => (hhd t (Ico_subset_Icc_self ht)).mono_of_mem_nhdsWithin
      (Icc_mem_nhdsGE_of_mem ht))
    (fun t ht => hhb t (Ico_subset_Icc_self ht))
  have hg0 := hge 0 ⟨le_rfl,hT⟩
  have hh0 := hhe 0 ⟨le_rfl,hT⟩
  simp only [intervalIntegral.integral_same, add_zero] at hg0 hh0
  exact hg0.trans hh0.symm

/-- Every two continuous solutions of the original full mild equation coincide
on their common finite interval, without an assumed common amplitude bound. -/
theorem mild_solution_unique {R T : ℝ} (hR : 0 ≤ R) (hT : 0 ≤ T)
    (c : ℝ) (f₀ : Distribution R) (f g : ℝ → Distribution R)
    (hfc : ContinuousOn f (Icc 0 T)) (hgc : ContinuousOn g (Icc 0 T))
    (hfe : ∀ t ∈ Icc 0 T, f t = transport R t f₀ +
      ∫ s in (0 : ℝ)..t, c • transport R (t-s) (collision R hR (f s)))
    (hge : ∀ t ∈ Icc 0 T, g t = transport R t f₀ +
      ∫ s in (0 : ℝ)..t, c • transport R (t-s) (collision R hR (g s))) :
    EqOn f g (Icc 0 T) := by
  have he := moving_frame_unique hR hT c f₀ (toFrame f) (toFrame g)
    (toFrame_continuousOn hfc) (toFrame_continuousOn hgc)
    (mild_to_moving_frame hR c f₀ f hfc hfe) (mild_to_moving_frame hR c f₀ g hgc hge)
  intro t ht
  have he' := congrArg (transport R t) (he ht)
  simpa only [fromFrame_toFrame] using he'

end
end Resonance.KineticUniqueness
