import Resonance.PositiveLossShift

/-! The actual five-moment augmentation remains invertible for every
nonnegative shift.  Its kernel proof retains the signed collision form
and the additional nonnegative loss-shift pairing. -/
open MeasureTheory Set
open scoped ENNReal BigOperators
namespace Resonance.ShiftedAugmentation
noncomputable section
set_option maxHeartbeats 1800000
open ResonantMeasure WeightedJointMeasure Thermodynamics ReferenceFrequencySpace CollisionFrequency
open ActualPairNormalization PhysicalFiveBasis PhysicalMomentProjection PhysicalProjectionKernel
open PhysicalFrequencyCoordinates PhysicalWeightedCoercivity ReferenceMomentFunctionals
open LinftyPhysicalDomain LinftyPhysicalForm PositiveLossShift LinftyFiveAugmentation

def shiftedCompact {R : ℝ} (hR : 0<R) {θ : Parameter} (hθ : θ∈positiveDomain R)
    {z : ℝ} (hz : 0≤z) : Lp ℝ ∞ (cubeVolume R)→L[ℝ]Lp ℝ ∞ (cubeVolume R) :=
  (compactPart hR hθ).comp (multiplier hR hθ hz)

def shiftedAugmented {R : ℝ} (hR : 0<R) {θ : Parameter} (hθ : θ∈positiveDomain R)
    {z : ℝ} (hz : 0≤z) : Lp ℝ ∞ (cubeVolume R)→L[ℝ]Lp ℝ ∞ (cubeVolume R) :=
  1+shiftedCompact hR hθ hz

theorem shiftedCompact_compact {R : ℝ} (hR : 0<R) {θ : Parameter}
    (hθ : θ∈positiveDomain R) {z : ℝ} (hz : 0≤z) :
    IsCompactOperator (shiftedCompact hR hθ hz) :=
  (compactPart_compact hR hθ).comp_clm (multiplier hR hθ hz)

theorem shiftedAugmented_zero {R : ℝ} (hR : 0<R) {θ : Parameter}
    (hθ : θ∈positiveDomain R) :
    shiftedAugmented hR hθ (show (0:ℝ)≤0 from le_rfl)=augmented hR hθ := by
  unfold shiftedAugmented shiftedCompact
  rw [multiplier_zero]
  ext f
  rfl

theorem shifted_pairing {R : ℝ} (hR : 0<R) {θ : Parameter}
    (hθ : θ∈positiveDomain R) {z : ℝ} (hz : 0≤z)
    (f : Lp ℝ ∞ (cubeVolume R)) (v : Space R) :
    (∫k,v k*(shiftedAugmented hR hθ hz f) k∂cubeVolume R)=
      physicalForm hR.le hθ (shiftedDivide hR hθ hz f) v+
        (∑i : Fin 5,(analysisMap hR hθ (shiftedDivide hR hθ hz f)) i*(analysisMap hR hθ v) i)+
          (∫k,v k*(f-multiplier hR hθ hz f) k∂cubeVolume R) := by
  let e := multiplier hR hθ hz f
  have hid : shiftedAugmented hR hθ hz f=augmented hR hθ e+(f-e) := by
    change f+compactPart hR hθ e=(e+compactPart hR hθ e)+(f-e)
    abel
  have ha : Integrable (fun k=>v k*(augmented hR hθ e) k) (cubeVolume R) := by
    exact ((divided_diagonal hR hθ (augmented hR hθ e) v).1).congr
      (ae_of_all _ (fun _=>mul_comm _ _))
  have hg : Integrable (fun k=>v k*(f-e) k) (cubeVolume R) := by
    exact ((divided_diagonal hR hθ (f-e) v).1).congr
      (ae_of_all _ (fun _=>mul_comm _ _))
  rw [hid]
  have he : (fun k=>v k*(augmented hR hθ e+(f-e)) k)=ᵐ[cubeVolume R]
      (fun k=>v k*(augmented hR hθ e) k+v k*(f-e) k) := by
    filter_upwards [Lp.coeFn_add (augmented hR hθ e) (f-e)] with k hk
    simp only [Pi.add_apply] at hk
    rw [hk,mul_add]
  rw [integral_congr_ae he,integral_add ha hg,augmented_pairing hR hθ e v]
  rfl

theorem shift_gap_nonnegative {R : ℝ} (hR : 0<R) {θ : Parameter}
    (hθ : θ∈positiveDomain R) {z : ℝ} (hz : 0≤z) (f : Lp ℝ ∞ (cubeVolume R)) :
    0≤∫k,shiftedDivide hR hθ hz f k*(f-multiplier hR hθ hz f) k∂cubeVolume R := by
  apply integral_nonneg_of_ae
  filter_upwards [shiftedDivide_ae hR hθ hz f,multiplier_ae hR hθ hz f,
    Lp.coeFn_sub f (multiplier hR hθ hz f),loss_positive_ae hR hθ]
      with k hu hm hs hn
  simp only [Pi.sub_apply] at hs
  rw [hu,hs,hm]
  have hd := (add_pos_of_pos_of_nonneg hn hz).ne'
  have he : f k/(lossFrequency R (profile θ) k+z)*(f k-f k*fraction R θ z k)=
      z*(f k/(lossFrequency R (profile θ) k+z))^2 := by
    unfold fraction
    field_simp
    ring
  rw [he]
  positivity

theorem shiftedAugmented_kernel_zero {R : ℝ} (hR : 0<R) {θ : Parameter}
    (hθ : θ∈positiveDomain R) {z : ℝ} (hz : 0≤z) {f : Lp ℝ ∞ (cubeVolume R)}
    (hf : shiftedAugmented hR hθ hz f=0) : f=0 := by
  let e := multiplier hR hθ hz f
  let u := shiftedDivide hR hθ hz f
  let a := analysisMap hR hθ u
  have he := shifted_pairing hR hθ hz f u
  rw [hf] at he
  have hz0 : (∫k,u k*(0 : Lp ℝ ∞ (cubeVolume R)) k∂cubeVolume R)=0 := by
    calc
      _ = ∫k,(0:ℝ)∂cubeVolume R := by
        apply integral_congr_ae
        filter_upwards [Lp.coeFn_zero ℝ ∞ (cubeVolume R)] with k hk
        simp only [hk,Pi.zero_apply,mul_zero]
      _ = 0 := integral_zero _ _
  rw [hz0,physical_form_square] at he
  have hs : 0≤∑i : Fin 5,a i*a i := Finset.sum_nonneg (fun i _=>mul_self_nonneg (a i))
  have hg := shift_gap_nonnegative hR hθ hz f
  have hd : physicalDifference hR.le hθ u=0 := by
    apply norm_eq_zero.mp
    nlinarith [norm_nonneg (physicalDifference hR.le hθ u)]
  have haz : a=0 := by
    have hh : ∑i : Fin 5,a i*a i=0 := by nlinarith [sq_nonneg ‖physicalDifference hR.le hθ u‖]
    funext i
    have hi := (Finset.sum_eq_zero_iff_of_nonneg (fun i _=>mul_self_nonneg (a i))).mp hh i (Finset.mem_univ i)
    exact mul_self_eq_zero.mp hi
  have hu : u=0 := by
    rw [←projection_fixed_kernel hR hθ hd]
    change synthesis hR.le hθ (gramInverse hR hθ a)=0
    rw [haz,map_zero,map_zero]
  have he0 : e=0 := by
    apply divide_injective hR hθ
    simpa only [map_zero] using hu
  change f+compactPart hR hθ e=0 at hf
  simpa only [he0,map_zero,add_zero] using hf

theorem shiftedAugmented_bijective {R : ℝ} (hR : 0<R) {θ : Parameter}
    (hθ : θ∈positiveDomain R) {z : ℝ} (hz : 0≤z) :
    Function.Bijective (shiftedAugmented hR hθ hz) := by
  have hn : ¬Module.End.HasEigenvalue (shiftedCompact hR hθ hz).toLinearMap (-1) := by
    rw [Module.End.hasEigenvalue_iff,not_not]
    apply le_antisymm ?_ bot_le
    intro f hf
    change f=0
    apply shiftedAugmented_kernel_zero hR hθ hz
    have he := Module.End.mem_eigenspace_iff.mp hf
    change shiftedCompact hR hθ hz f=(-1 : ℝ) • f at he
    change f+shiftedCompact hR hθ hz f=0
    rw [he,neg_one_smul,add_neg_cancel]
  have hr := ((shiftedCompact_compact hR hθ hz).hasEigenvalue_or_mem_resolventSet
    (by norm_num : (-1 : ℝ)≠0)).resolve_left hn
  rw [spectrum.mem_resolventSet_iff] at hr
  have he : algebraMap ℝ (Lp ℝ ∞ (cubeVolume R)→L[ℝ]Lp ℝ ∞ (cubeVolume R)) (-1)-
      shiftedCompact hR hθ hz= -(shiftedAugmented hR hθ hz) := by
    apply ContinuousLinearMap.ext
    intro f
    change (-1 : ℝ) • f-shiftedCompact hR hθ hz f= -(f+shiftedCompact hR hθ hz f)
    rw [neg_one_smul]
    abel
  rw [he,IsUnit.neg_iff,ContinuousLinearMap.isUnit_iff_bijective] at hr
  exact hr

def shiftedEquiv {R : ℝ} (hR : 0<R) {θ : Parameter} (hθ : θ∈positiveDomain R)
    {z : ℝ} (hz : 0≤z) : Lp ℝ ∞ (cubeVolume R)≃L[ℝ]Lp ℝ ∞ (cubeVolume R) :=
  ContinuousLinearEquiv.ofBijective (shiftedAugmented hR hθ hz)
    (LinearMap.ker_eq_bot.mpr (shiftedAugmented_bijective hR hθ hz).1)
    (LinearMap.range_eq_top.mpr (shiftedAugmented_bijective hR hθ hz).2)

end
end Resonance.ShiftedAugmentation
