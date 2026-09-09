import Resonance.FreeTransport

/-! Joint strong continuity and the exact Duhamel change of variables for
the original transport group. No operator-norm continuity of translations is
assumed. The source remains on the same phase space and the same time axis. -/
open MeasureTheory
open scoped Interval

namespace Resonance.TransportDuhamel
noncomputable section
open FreeTransport

theorem transport_joint_continuous (R : ℝ) :
    Continuous (fun q : ℝ × Distribution R => transport R q.1 q.2) := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  have hc : Continuous (fun q : (ℝ × Distribution R) × Phase R =>
      characteristic q.1.1 q.2) :=
    (characteristic_joint_continuous R).comp (continuous_fst.fst.prodMk continuous_snd)
  exact continuous_fst.snd.eval hc

theorem moving_source_continuousOn (R : ℝ) {F : ℝ → Distribution R} {t : ℝ}
    (hF : ContinuousOn F (Set.uIcc 0 t)) :
    ContinuousOn (fun s => transport R (-s) (F s)) (Set.uIcc 0 t) :=
  (transport_joint_continuous R).comp_continuousOn (continuous_neg.continuousOn.prodMk hF)

theorem moving_source_intervalIntegrable (R : ℝ) {F : ℝ → Distribution R} {t : ℝ}
    (hF : ContinuousOn F (Set.uIcc 0 t)) :
    IntervalIntegrable (fun s => transport R (-s) (F s)) volume 0 t :=
  (moving_source_continuousOn R hF).intervalIntegrable

theorem retarded_source_intervalIntegrable (R : ℝ) {F : ℝ → Distribution R} {t : ℝ}
    (hF : ContinuousOn F (Set.uIcc 0 t)) :
    IntervalIntegrable (fun s => transport R (t-s) (F s)) volume 0 t :=
  ((transport_joint_continuous R).comp_continuousOn
    ((continuous_const.sub continuous_id).continuousOn.prodMk hF)).intervalIntegrable

theorem transport_integral (R : ℝ) (t : ℝ) {F : ℝ → Distribution R}
    (hF : ContinuousOn F (Set.uIcc 0 t)) :
    transport R t (∫ s in (0 : ℝ)..t, transport R (-s) (F s)) =
      ∫ s in (0 : ℝ)..t, transport R (t-s) (F s) := by
  have he := (transportCLM R t).intervalIntegral_comp_comm
    (moving_source_intervalIntegrable R hF)
  change (∫ s in (0 : ℝ)..t, transport R t (transport R (-s) (F s))) =
    transport R t (∫ s in (0 : ℝ)..t, transport R (-s) (F s)) at he
  rw [← he]
  apply intervalIntegral.integral_congr
  intro s _
  change transport R t (transport R (-s) (F s)) = transport R (t-s) (F s)
  rw [transport_add_time, sub_eq_add_neg]

theorem duhamel_identity (R : ℝ) (t : ℝ) (f₀ : Distribution R)
    {F : ℝ → Distribution R} (hF : ContinuousOn F (Set.uIcc 0 t)) :
    transport R t (f₀ + ∫ s in (0 : ℝ)..t, transport R (-s) (F s)) =
      transport R t f₀ + ∫ s in (0 : ℝ)..t, transport R (t-s) (F s) := by
  rw [transport_add, transport_integral R t hF]

/-- A source curve expressed in the moving frame gives the actual original
transport Duhamel equation, with all source times kept in one integral. -/
theorem moving_frame_solution_to_duhamel (R : ℝ) (t : ℝ) (f₀ : Distribution R)
    {g F : ℝ → Distribution R} (hF : ContinuousOn F (Set.uIcc 0 t))
    (hg : g t = f₀ + ∫ s in (0 : ℝ)..t, transport R (-s) (F s)) :
    transport R t (g t) = transport R t f₀ +
      ∫ s in (0 : ℝ)..t, transport R (t-s) (F s) := by
  rw [hg]
  exact duhamel_identity R t f₀ hF

end
end Resonance.TransportDuhamel
