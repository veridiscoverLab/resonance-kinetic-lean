import Resonance.CornerNewtonEnergy

/-! The first Newton kernel and the explicit logarithmic tail sum.
The spatial estimate is uniform in the output point on all of E. -/
open Real Set MeasureTheory Metric
open scoped ENNReal Topology
namespace Resonance.NewtonPotentialTails
noncomputable section
set_option maxHeartbeats 1000000
open Resonance.ResonantMeasure Resonance.NewtonKernelBalls
open Resonance.NewtonLayerEnergy

def kernelOne (x:E) : ℝ≥0∞ := ENNReal.ofReal (‖x‖⁻¹)

theorem kernelOne_measurable : Measurable kernelOne := by unfold kernelOne; fun_prop

theorem kernelOne_inside {r:ℝ} (hr:0<r) {x:E} (hx:‖x‖≤r) :
    kernelOne x≤ENNReal.ofReal r*kernelTwo x := by
  unfold kernelOne kernelTwo
  rw [←ENNReal.ofReal_mul hr.le]
  apply ENNReal.ofReal_le_ofReal
  by_cases hn:‖x‖=0
  · simp [hn]
  · have hp:0<‖x‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hn)
    have hh : ‖x‖⁻¹≤r*‖x‖⁻¹^2 := by
      rw [inv_pow,←div_eq_mul_inv]
      apply (le_div_iff₀ (sq_pos_of_pos hp)).mpr
      simpa only [pow_two,inv_mul_cancel_left₀ hp.ne'] using hx
    exact hh

theorem kernelOne_outside {r:ℝ} (hr:0<r) {x:E} (hx:r≤‖x‖) :
    kernelOne x≤ENNReal.ofReal r⁻¹ :=
  ENNReal.ofReal_le_ofReal (inv_anti₀ hr hx)

theorem kernelOne_set_bound {r C:ℝ} (hr:0<r) (hC:0≤C) (S:Set E)
    (hS:MeasurableSet S) (hvol:volume S≤ENNReal.ofReal (C*r^3)) (k:E) :
    (∫⁻p in S,kernelOne (k-p))≤ENNReal.ofReal ((sphereArea+C)*r^2) := by
  classical
  let f : E→ℝ≥0∞ := fun p=>kernelOne (k-p)
  let g : E→ℝ≥0∞ := fun p=>ENNReal.ofReal r*kernelTwo (k-p)
  have hg : Measurable g := measurable_const.mul
    (kernelTwo_measurable.comp (measurable_const.sub measurable_id))
  have hp (p:E) : S.indicator f p≤
      (ball k r).indicator g p+S.indicator (fun _=>ENNReal.ofReal r⁻¹) p := by
    by_cases hs:p∈S
    · rw [Set.indicator_of_mem hs,Set.indicator_of_mem hs]
      by_cases hb:p∈ball k r
      · rw [Set.indicator_of_mem hb]
        apply (kernelOne_inside hr ?_).trans le_self_add
        have hh : dist p k<r := hb
        simpa only [dist_eq_norm,norm_sub_rev] using hh.le
      · rw [Set.indicator_of_notMem hb,zero_add]
        apply kernelOne_outside hr
        have hh : r≤dist p k := le_of_not_gt hb
        simpa only [dist_eq_norm,norm_sub_rev] using hh
    · rw [Set.indicator_of_notMem hs]
      exact zero_le _
  have hI := lintegral_mono (μ:=(volume:Measure E)) hp
  rw [lintegral_indicator hS,lintegral_add_left (hg.indicator measurableSet_ball),
    lintegral_indicator measurableSet_ball,lintegral_indicator hS,lintegral_const,
    Measure.restrict_apply_univ] at hI
  change (∫⁻p in S,kernelOne (k-p))≤
    (∫⁻p in ball k r,ENNReal.ofReal r*kernelTwo (k-p))+ENNReal.ofReal r⁻¹*volume S at hI
  rw [lintegral_const_mul _ (show Measurable (fun p:E=>kernelTwo (k-p)) from
    kernelTwo_measurable.comp (measurable_const.sub measurable_id)),kernelTwo_ball hr] at hI
  have he : ENNReal.ofReal r*(surface univ*ENNReal.ofReal r)+
      ENNReal.ofReal r⁻¹*ENNReal.ofReal (C*r^3)=
      ENNReal.ofReal ((sphereArea+C)*r^2) := by
    rw [←ofReal_sphereArea,←ENNReal.ofReal_mul sphereArea_nonnegative,
      ←ENNReal.ofReal_mul hr.le,←ENNReal.ofReal_mul (inv_nonneg.mpr hr.le),
      ←ENNReal.ofReal_add (by have hh:=sphereArea_nonnegative; positivity) (by positivity)]
    congr 1
    field_simp
  exact (hI.trans (add_le_add le_rfl (mul_le_mul_right hvol _))).trans_eq he

theorem inverse_square_le_telescope {a:ℝ} (ha:0<a) :
    1/(a+1)^2≤1/a-1/(a+1) := by
  have ha1:0<a+1 := by linarith
  apply (div_le_iff₀ (sq_pos_of_pos ha1)).mpr
  field_simp
  nlinarith

theorem one_add_kernelOne_set_bound {r C:ℝ} (hr:0<r) (hr1:r≤1) (hC:0≤C) (S:Set E)
    (hS:MeasurableSet S) (hvol:volume S≤ENNReal.ofReal (C*r^3)) (k:E) :
    (∫⁻p in S,1+kernelOne (k-p))≤ENNReal.ofReal ((sphereArea+2*C)*r^2) := by
  rw [lintegral_add_left measurable_const,lintegral_const,one_mul,Measure.restrict_apply_univ]
  apply (add_le_add hvol (kernelOne_set_bound hr hC S hS hvol k)).trans
  have ha:=sphereArea_nonnegative
  rw [←ENNReal.ofReal_add (by positivity) (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  have hh:=mul_le_mul_of_nonneg_left hr1 (show 0≤C*r^2 by positivity)
  nlinarith

theorem inverse_square_range_bound (N m:ℕ) :
    (∑j∈Finset.range m,1/(((N+j:ℕ):ℝ)+8)^2)≤
      1/((N:ℝ)+7)-1/(((N+m:ℕ):ℝ)+7) := by
  induction m with
  | zero => simp
  | succ m hm =>
    rw [Finset.sum_range_succ]
    have ht := inverse_square_le_telescope (show 0<((N+m:ℕ):ℝ)+7 by positivity)
    norm_num only [Nat.cast_add,Nat.cast_one] at hm ht ⊢
    have he : (N:ℝ)+m+7+1=(N:ℝ)+m+8 := by ring
    rw [he] at ht
    convert add_le_add hm ht using 1
    ring

theorem inverse_square_tail_bound (N:ℕ) :
    (∑'j:ℕ,ENNReal.ofReal (1/(((N+j:ℕ):ℝ)+8)^2))≤
      ENNReal.ofReal (1/((N:ℝ)+7)) := by
  apply ENNReal.tsum_le_of_sum_range_le
  intro m
  rw [←ENNReal.ofReal_sum_of_nonneg (fun j _=>by positivity)]
  apply ENNReal.ofReal_le_ofReal
  apply (inverse_square_range_bound N m).trans
  have hpos:0≤1/(((N+m:ℕ):ℝ)+7) := by positivity
  linarith

end
end Resonance.NewtonPotentialTails
