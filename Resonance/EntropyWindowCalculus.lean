import Resonance.PhaseCollisionEntropy

/-! Endpoint-correct entropy integration on the original closed time
window. Differentiability is only required within that window. -/
open Set MeasureTheory
namespace Resonance.EntropyWindowCalculus
noncomputable section
open FreeTransport PhaseEnergy ContinuousLogPath PhaseCollisionEntropy

theorem phaseProduction_continuousOn {R : ℝ} (hR : 0 ≤ R) {s : Set ℝ}
    {f : ℝ→Distribution R} (hf : ContinuousOn f s)
    (hp : ∀ t∈s,∀ z,0 < f t z) :
    ContinuousOn (fun t=>phaseProduction R (f t)) s := by
  have hc := (SpatialCollision.collision_continuous hR).comp_continuousOn hf
  have hi := inversePath_continuousOn hf (fun t ht z=>(hp t ht z).ne')
  have h := (integralCLM R).continuous.comp_continuousOn (hc.mul hi)
  exact h.congr (fun t ht=>(phase_collision_production hR (f t) (hp t ht)).symm)

theorem integrate_entropy_balance {T c : ℝ} (hT : 0 ≤ T) (H D W : ℝ→ℝ)
    (hD : ContinuousOn D (Icc 0 T)) (hW : ContinuousOn W (Icc 0 T))
    (hH : ∀ t∈Icc 0 T,HasDerivWithinAt H (-c*D t+W t) (Icc 0 T) t) :
    H T+c*(∫ t in (0 : ℝ)..T,D t)=H 0+∫ t in (0 : ℝ)..T,W t := by
  have hiD : IntervalIntegrable D volume 0 T := by
    apply ContinuousOn.intervalIntegrable
    simpa only [uIcc_of_le hT] using hD
  have hiW : IntervalIntegrable W volume 0 T := by
    apply ContinuousOn.intervalIntegrable
    simpa only [uIcc_of_le hT] using hW
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hT
    (fun t ht=>(hH t ht).continuousWithinAt)
    (fun t ht=>(hH t (Ioo_subset_Icc_self ht)).hasDerivAt (Icc_mem_nhds ht.1 ht.2))
    ((hiD.const_mul (-c)).add hiW)
  rw [intervalIntegral.integral_add (hiD.const_mul (-c)) hiW,
    intervalIntegral.integral_const_mul] at he
  linarith

end
end Resonance.EntropyWindowCalculus
