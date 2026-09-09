import Resonance.KineticField

/-! Local solutions of the original, spatially inhomogeneous, sharp-cutoff
four-wave kinetic equation. The vector field, its modulus, and its time of
existence are constructed from the actual collision operator, with no assumed
existence or amplitude-control interface. -/
open Set Metric MeasureTheory
open scoped NNReal Interval

namespace Resonance.LocalKinetics
noncomputable section
open FreeTransport SpatialCollision KineticField TransportDuhamel

theorem exists_moving_frame_solution (R : ℝ) (hR : 0 ≤ R) (c : ℝ)
    (f₀ : Distribution R) (a : ℝ≥0) (ha : 0 < a) :
    ∃ g : ℝ → Distribution R, Continuous g ∧ g 0 = f₀ ∧
      (∀ t, ‖g t - f₀‖ ≤ a) ∧
      ∀ t ∈ Icc 0 (localTime R c f₀ a),
        g t = f₀ + ∫ s in (0 : ℝ)..t, field R hR c s (g s) := by
  let hp := actual_picardLindelof R hR c f₀ a ha
  have hx : f₀ ∈ closedBall f₀ (0 : ℝ) := mem_closedBall_self le_rfl
  obtain ⟨α,hα⟩ := ODE.FunSpace.exists_isFixedPt_next hp hx
  refine ⟨α.compProj, α.continuous_compProj, ?_, ?_, ?_⟩
  · rw [ODE.FunSpace.compProj_of_mem (show 0 ∈ Icc 0 (localTime R c f₀ a) from
      ⟨le_rfl, (localTime_pos f₀ ha).le⟩)]
    exact α.apply_of_zero
  · intro t
    exact mem_closedBall_iff_norm.mp (α.compProj_mem_closedBall hp.mul_max_le)
  · intro t ht
    rw [ODE.FunSpace.compProj_of_mem ht]
    exact (ODE.FunSpace.isFixedPt_next_iff hp hx).mp hα ⟨t,ht⟩

theorem exists_mild_solution (R : ℝ) (hR : 0 ≤ R) (c : ℝ)
    (f₀ : Distribution R) (a : ℝ≥0) (ha : 0 < a) :
    ∃ f : ℝ → Distribution R, Continuous f ∧ f 0 = f₀ ∧
      (∀ t, ‖f t - transport R t f₀‖ ≤ a) ∧
      (∀ t, ‖f t‖ ≤ ‖f₀‖ + a) ∧
      ∀ t ∈ Icc 0 (localTime R c f₀ a),
        f t = transport R t f₀ +
          ∫ s in (0 : ℝ)..t, c • transport R (t-s) (collision R hR (f s)) := by
  obtain ⟨g,hgc,hg0,hgb,hge⟩ := exists_moving_frame_solution R hR c f₀ a ha
  let f : ℝ → Distribution R := fun t => transport R t (g t)
  have hfc : Continuous f := (transport_joint_continuous R).comp (continuous_id.prodMk hgc)
  have hfb : ∀ t, ‖f t - transport R t f₀‖ ≤ a := by
    intro t
    change ‖transportCLM R t (g t) - transportCLM R t f₀‖ ≤ _
    rw [← map_sub]
    change ‖transport R t (g t - f₀)‖ ≤ _
    rw [transport_norm]
    exact hgb t
  refine ⟨f,hfc,?_,hfb,?_,?_⟩
  · change transport R 0 (g 0) = f₀
    rw [hg0, transport_zero]
  · intro t
    calc
      ‖f t‖ ≤ ‖f t - transport R t f₀‖ + ‖transport R t f₀‖ :=
        norm_le_norm_sub_add _ _
      _ ≤ _ := by rw [transport_norm]; linarith [hfb t]
  · intro t ht
    let F : ℝ → Distribution R := fun s => c • collision R hR (f s)
    have hF : Continuous F := ((collision_continuous hR).comp hfc).const_smul c
    have he : g t = f₀ + ∫ s in (0 : ℝ)..t, transport R (-s) (F s) := by
      rw [hge t ht]
      congr 1
    change transport R t (g t) = _
    rw [moving_frame_solution_to_duhamel R t f₀ hF.continuousOn he]
    congr 1

/-- Uniformly positive input admits a positive solution on an explicit time interval.
The equation holds only on that interval; the continuous extension outside is
used solely to state Banach-valued derivatives and integrals. -/
theorem exists_positive_mild_solution (R : ℝ) (hR : 0 ≤ R) (c : ℝ)
    (f₀ : Distribution R) (m : ℝ) (hm : 0 < m) (hf₀ : ∀ p, m ≤ f₀ p) :
    ∃ T : ℝ, 0 < T ∧ ∃ f : ℝ → Distribution R,
      Continuous f ∧ f 0 = f₀ ∧
      (∀ t ∈ Icc 0 T, ∀ p, m/2 ≤ f t p) ∧
      (∀ t ∈ Icc 0 T, ‖f t‖ ≤ ‖f₀‖ + m/2) ∧
      ∀ t ∈ Icc 0 T,
        f t = transport R t f₀ +
          ∫ s in (0 : ℝ)..t, c • transport R (t-s) (collision R hR (f s)) := by
  let a : ℝ≥0 := ⟨m/2, by positivity⟩
  have ha : 0 < a := by change 0 < m/2; positivity
  obtain ⟨f,hfc,hf0,hfb,hfn,hfe⟩ := exists_mild_solution R hR c f₀ a ha
  refine ⟨localTime R c f₀ a, localTime_pos f₀ ha, f, hfc, hf0, ?_, ?_, hfe⟩
  · intro t _ p
    have hb := ((f t - transport R t f₀).norm_coe_le_norm p).trans (hfb t)
    change ‖f t p - transport R t f₀ p‖ ≤ m/2 at hb
    have hlo := (abs_le.mp (show |f t p - transport R t f₀ p| ≤ m/2 from hb)).1
    have hinit := hf₀ (characteristic t p)
    change m ≤ transport R t f₀ p at hinit
    linarith
  · intro t _
    exact hfn t

end
end Resonance.LocalKinetics
