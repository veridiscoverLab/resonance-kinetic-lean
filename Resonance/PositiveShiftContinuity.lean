import Resonance.ShiftedDivideLimit
import Resonance.ShiftedAugmentation

/-! Positive-shift continuity and the zero endpoint are treated separately:
the original loss multiplier itself does not converge in L-infinity at zero. -/
open MeasureTheory Set Filter
open scoped ENNReal Topology
namespace Resonance.PositiveShiftContinuity
noncomputable section
set_option maxHeartbeats 1800000
open ResonantMeasure Thermodynamics WeightedJointMeasure CollisionFrequency
open ActualPairNormalization PositiveLossShift ShiftedAugmentation LinftyFiveAugmentation

theorem multiplier_shift_difference_bound {R : ℝ} (hR : 0<R) {θ : Parameter}
    (hθ : θ∈positiveDomain R) {z w : ℝ} (hz : 0≤z) (hw : 0<w) :
    ‖multiplier hR hθ hz-multiplier hR hθ hw.le‖≤|z-w|/w := by
  apply CubeLinftyMultiplier.operator_difference_bound _ _ (by positivity)
  filter_upwards [LinftyPhysicalDomain.loss_positive_ae hR hθ,
    ae_restrict_mem (measurable_cube R)] with k hn hk
  have hdz := (add_pos_of_pos_of_nonneg hn hz).ne'
  have hdw := (add_pos hn hw).ne'
  have he : fraction R θ z k-fraction R θ w k=
      fraction R θ z k*(w-z)/(lossFrequency R (profile θ) k+w) := by
    unfold fraction
    field_simp
    ring
  rw [Real.norm_eq_abs,he,abs_div,abs_mul,
    abs_of_nonneg (fraction_bounds hR hθ hz hk).1,abs_of_pos (add_pos hn hw),abs_sub_comm w z]
  calc
    _ ≤ |z-w|/(lossFrequency R (profile θ) k+w) := by
      gcongr
      exact (mul_le_of_le_one_left (abs_nonneg _) (fraction_bounds hR hθ hz hk).2)
    _ ≤ |z-w|/w := div_le_div_of_nonneg_left (abs_nonneg _) hw (by linarith)

theorem multiplier_continuousAt_pos {R : ℝ} (hR : 0<R) {θ : Parameter}
    (hθ : θ∈positiveDomain R) (w : Set.Ici (0:ℝ)) (hw : 0<(w:ℝ)) :
    ContinuousAt (fun z : Set.Ici (0:ℝ)=>multiplier hR hθ z.property) w := by
  apply (tendsto_iff_norm_sub_tendsto_zero
    (E := Lp ℝ ∞ (cubeVolume R)→L[ℝ]Lp ℝ ∞ (cubeVolume R))).mpr
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have ht : Tendsto (fun z : Set.Ici (0:ℝ)=>|(z:ℝ)-(w:ℝ)|) (𝓝 w) (𝓝 0) := by
    simpa using ((continuous_subtype_val.tendsto w).sub
      (tendsto_const_nhds (x:=(w:ℝ)))).abs
  filter_upwards [ht.eventually (gt_mem_nhds (mul_pos hε hw))] with z hz
  rw [Real.dist_eq,sub_zero,abs_of_nonneg (norm_nonneg _)]
  apply (multiplier_shift_difference_bound hR hθ z.property hw).trans_lt
  exact (div_lt_iff₀ hw).mpr hz

theorem shiftedCompact_continuousAt_zero {R : ℝ} (hR : 0<R) {θ : Parameter}
    (hθ : θ∈positiveDomain R) :
    Tendsto (fun z : Set.Ici (0:ℝ)=>shiftedCompact hR hθ z.property)
      (𝓝 ⟨0,show (0:ℝ)≤0 from le_rfl⟩) (𝓝 (compactPart hR hθ)) := by
  have ha := ShiftedOperatorLimit.actual_shifted_operator_continuousAt_zero hR hθ
  have hd := ShiftedDivideLimit.actual_shiftedDivide_continuousAt_zero hR hθ
  have hc : Continuous (fun D : Lp ℝ ∞ (cubeVolume R)→L[ℝ]ReferenceFrequencySpace.Space R=>
      (synthesisTop hθ).comp ((PhysicalFiveBasis.analysisMap hR hθ).comp D)) :=
    continuous_const.clm_comp (continuous_const.clm_comp continuous_id)
  have hh := ha.add (hc.continuousAt.tendsto.comp hd)
  convert hh using 1

theorem shiftedCompact_continuous {R : ℝ} (hR : 0<R) {θ : Parameter}
    (hθ : θ∈positiveDomain R) :
    Continuous (fun z : Set.Ici (0:ℝ)=>shiftedCompact hR hθ z.property) := by
  apply continuous_iff_continuousAt.mpr
  intro w
  by_cases hw : (w:ℝ)=0
  · have he : w=⟨0,show (0:ℝ)≤0 from le_rfl⟩ := Subtype.ext hw
    subst w
    change Tendsto _ _ _
    convert shiftedCompact_continuousAt_zero hR hθ using 1
    congr 1
    unfold shiftedCompact
    change (compactPart hR hθ).comp (multiplier hR hθ (show (0:ℝ)≤0 from le_rfl))=_
    rw [multiplier_zero]
    ext f
    rfl
  · exact continuousAt_const.clm_comp (multiplier_continuousAt_pos hR hθ w
      (lt_of_le_of_ne w.property (Ne.symm hw)))

theorem shiftedAugmented_continuous {R : ℝ} (hR : 0<R) {θ : Parameter}
    (hθ : θ∈positiveDomain R) :
    Continuous (fun z : Set.Ici (0:ℝ)=>shiftedAugmented hR hθ z.property) :=
  continuous_const.add (shiftedCompact_continuous hR hθ)

end
end Resonance.PositiveShiftContinuity
