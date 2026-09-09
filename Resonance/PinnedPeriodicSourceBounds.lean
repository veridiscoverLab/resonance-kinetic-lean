import Resonance.PinnedClassificationFinal
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp

/-! Quantitative local source bounds come from the original normalized
circle L² norm.  Finite winding is proved for every fixed real interval;
no independent bound on a lifted source is assumed. -/
open Real MeasureTheory Set Filter
open scoped ENNReal NNReal Topology
namespace Resonance.PinnedPeriodicSourceBounds
noncomputable section
open Resonance.PinnedPeriodicity Resonance.PinnedCircleAE
open Resonance.PinnedClassificationFinal
local instance periodPositive : Fact (0 < period) := ⟨period_pos⟩

theorem periodic_local_L1_bound {T : ℝ} (hT : 0<T) {a b : ℝ} (hab : a≤b) :
    ∃ C : ℝ≥0∞, C≠⊤ ∧ ∀ f : ℝ→ℂ, Function.Periodic f T →
      IntervalIntegrable f volume 0 T →
      Integrable f (volume.restrict (Icc a b)) ∧
      eLpNorm f 1 (volume.restrict (Icc a b)) ≤
        C*eLpNorm f 1 (volume.restrict (Ioc 0 T)) := by
  obtain ⟨n,hn⟩ := exists_nat_ge ((b-a)/T)
  have hbn : b≤a+(n:ℝ)*T := by
    have := (div_le_iff₀ hT).mp hn
    linarith
  refine ⟨n, by finiteness, ?_⟩
  intro f hp hi
  have hall := hp.intervalIntegrable₀ hT.ne' hi
  have hic : Integrable f (volume.restrict (Icc a b)) :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hab).mp (hall a b)
  refine ⟨hic,?_⟩
  have hpn : Function.Periodic (fun x => ‖f x‖) T := hp.comp norm
  have hle := intervalIntegral.integral_mono_interval (f:=fun x=>‖f x‖)
    le_rfl hab hbn (Filter.Eventually.of_forall (fun _=>norm_nonneg _))
    ((hall a (a+(n:ℝ)*T)).norm)
  have he := hpn.intervalIntegral_add_zsmul_eq (n:ℤ) a (fun x y=>(hall x y).norm)
  have hperiod := hpn.intervalIntegral_add_eq a 0
  simp only [zero_add] at hperiod
  simp only [zsmul_eq_mul, Int.cast_natCast] at he
  rw [he,hperiod] at hle
  have hreal : (∫ x in Icc a b, ‖f x‖) ≤
      (n:ℝ)*(∫ x in Ioc 0 T, ‖f x‖) := by
    simpa only [intervalIntegral.integral_of_le hab,
      intervalIntegral.integral_of_le hT.le,integral_Icc_eq_integral_Ioc] using hle
  rw [eLpNorm_one_eq_lintegral_enorm,eLpNorm_one_eq_lintegral_enorm,
    ←ofReal_integral_norm_eq_lintegral_enorm hic,
    ←ofReal_integral_norm_eq_lintegral_enorm
      ((intervalIntegrable_iff_integrableOn_Ioc_of_le hT.le).mp hi)]
  simpa only [ENNReal.ofReal_mul (Nat.cast_nonneg n), ENNReal.ofReal_natCast]
    using ENNReal.ofReal_le_ofReal hreal

theorem circleVolume_eq_period_smul_Haar :
    circleVolume = ENNReal.ofReal period • circleHaar := by
  rw [circleHaar,smul_smul,ENNReal.mul_inv_cancel
    (ne_of_gt (ENNReal.ofReal_pos.mpr period_pos)) ENNReal.ofReal_ne_top,one_smul]

/-- Every compact lifted source interval has a uniform L¹ bound in terms
of the same original probability-Haar L² norm. -/
theorem circle_L2_local_source_bound {a b : ℝ} (hab : a≤b) :
    ∃ C : ℝ≥0∞, C≠⊤ ∧ ∀ φ : PinnedPeriodicity.Circle→ℂ, MemLp φ 2 circleHaar →
      Integrable (periodicLift φ) (volume.restrict (Icc a b)) ∧
      eLpNorm (periodicLift φ) 1 (volume.restrict (Icc a b)) ≤
        C*eLpNorm φ 2 circleHaar := by
  obtain ⟨C,hC,hall⟩ := periodic_local_L1_bound period_pos hab
  refine ⟨C*ENNReal.ofReal period,ENNReal.mul_ne_top hC ENNReal.ofReal_ne_top,?_⟩
  intro φ hφ
  have hiH : Integrable φ circleHaar := hφ.integrable (by norm_num)
  have hiV : Integrable φ circleVolume := by
    rw [circleVolume_eq_period_smul_Haar]
    exact hiH.smul_measure ENNReal.ofReal_ne_top
  have mp := AddCircle.measurePreserving_mk period 0
  have hi0 : IntervalIntegrable (periodicLift φ) volume 0 period := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le period_pos.le]
    simpa only [zero_add] using (mp.integrable_comp hiV.aestronglyMeasurable).mpr hiV
  obtain ⟨hi,hle⟩ := hall (periodicLift φ) (periodicLift_periodic φ) hi0
  refine ⟨hi,hle.trans ?_⟩
  have he : eLpNorm (periodicLift φ) 1 (volume.restrict (Ioc 0 period)) =
      eLpNorm φ 1 circleVolume := by
    simpa only [zero_add] using eLpNorm_comp_measurePreserving
      (p:=1) hiV.aestronglyMeasurable mp
  rw [he,circleVolume_eq_period_smul_Haar,eLpNorm_one_smul_measure]
  have h12 := eLpNorm_le_eLpNorm_of_exponent_le (p:=1) (q:=2)
    (by norm_num) hφ.aestronglyMeasurable
  calc
    _ ≤ C*(ENNReal.ofReal period*eLpNorm φ 2 circleHaar) := by gcongr
    _ = _ := by ac_rfl

theorem circle_L2_lift_locallyIntegrable {φ : PinnedPeriodicity.Circle→ℂ}
    (hφ : MemLp φ 2 circleHaar) : LocallyIntegrable (periodicLift φ) volume := by
  rw [locallyIntegrable_iff]
  intro K hK
  obtain ⟨B,hB⟩ := hK.exists_bound_of_continuousOn (f:=fun x:ℝ=>x) continuousOn_id
  let L := max B 1
  have hL : 0<L := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  obtain ⟨_C,_hC,hall⟩ := circle_L2_local_source_bound (by linarith : -L≤L)
  apply IntegrableOn.mono_set (hall φ hφ).1
  intro x hx
  exact abs_le.mp ((hB x hx).trans (le_max_left _ _))

end
end Resonance.PinnedPeriodicSourceBounds
