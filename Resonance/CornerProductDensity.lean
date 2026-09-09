import Resonance.CornerProductCoordinates

open Real Set MeasureTheory
open scoped ENNReal Topology
namespace Resonance.CornerProductDensity
noncomputable section
set_option maxHeartbeats 600000
open Resonance.CornerProductCoordinates

theorem lintegral_Ioo_split (a:ℝ) (f:ℝ→ℝ≥0∞) :
    (∫⁻x in Ioo 0 a,f x)=∫⁻x in Ioi (0:ℝ),if x<a then f x else 0 := by
  have hs : Iio a∩Ioi (0:ℝ)=Ioo 0 a := by ext x; simp [and_comm]
  rw [←hs,←Measure.restrict_restrict measurableSet_Iio,
    ←lintegral_indicator measurableSet_Iio]
  rfl

/-- The full positive rectangle, pushed through the actual product map,
has the displayed one-dimensional inverse-coordinate density. -/
theorem rectangle_product_lintegral {a b:ℝ} (hb:0<b)
    (F:ℝ→ℝ≥0∞) (hF:Measurable F) :
    (∫⁻x in Ioo 0 a,∫⁻y in Ioo 0 b,F (x*y))=
      ∫⁻t in Ioi (0:ℝ),F t*(∫⁻x in Ioo (t/b) a,ENNReal.ofReal (x⁻¹)) := by
  let H : ℝ×ℝ→ℝ≥0∞ := fun p=>
    if p.1<a ∧ 0<p.2 ∧ p.2<p.1*b then F p.2 else 0
  have hH : Measurable H := by
    apply Measurable.ite
    · exact (measurableSet_lt measurable_fst measurable_const).inter
        ((measurableSet_lt measurable_const measurable_snd).inter
          (measurableSet_lt measurable_snd (measurable_fst.mul_const b)))
    · exact hF.comp measurable_snd
    · exact measurable_const
  have hc := product_coordinate_lintegral H hH
  have hleft : (∫⁻x in Ioi (0:ℝ),∫⁻y:ℝ,H (x,x*y))=
      ∫⁻x in Ioo 0 a,∫⁻y in Ioo 0 b,F (x*y) := by
    rw [lintegral_Ioo_split]
    apply lintegral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hx0 : 0<x := hx
    by_cases ha:x<a
    · rw [if_pos ha,←lintegral_indicator measurableSet_Ioo]
      apply lintegral_congr
      intro y
      have hh : (x<a ∧ 0<x*y ∧ x*y<x*b) ↔ y∈Ioo 0 b := by
        simp only [ha,true_and,mul_pos_iff_of_pos_left hx0,mul_lt_mul_iff_right₀ hx0,mem_Ioo]
      simp only [H,hh,Set.indicator_apply]
    · simp [H,ha]
  rw [hleft] at hc
  rw [hc]
  have hK : Measurable (fun p:ℝ×ℝ=>ENNReal.ofReal (p.1⁻¹)*H p) := by fun_prop
  rw [lintegral_lintegral_swap hK.aemeasurable,
    ←lintegral_indicator measurableSet_Ioi]
  apply lintegral_congr
  intro t
  by_cases ht:0<t
  · rw [Set.indicator_of_mem (show t∈Ioi (0:ℝ) from ht)]
    rw [←lintegral_const_mul _ (by fun_prop : Measurable (fun x:ℝ=>ENNReal.ofReal (x⁻¹)))]
    have hs : Ioo (t/b) a⊆Ioi (0:ℝ) := by
      intro x hx
      exact (div_pos ht hb).trans hx.1
    rw [←Set.inter_eq_left.mpr hs,←Measure.restrict_restrict measurableSet_Ioo,
      ←lintegral_indicator measurableSet_Ioo]
    apply lintegral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hh : (x<a ∧ 0<t ∧ t<x*b) ↔ x∈Ioo (t/b) a := by
      rw [mem_Ioo]
      have he : t<x*b ↔ t/b<x := by rw [div_lt_iff₀ hb]
      simp only [ht,true_and,he,and_comm]
    simp only [H,hh,Set.indicator_apply]
    split_ifs <;> simp [mul_comm]
  · rw [Set.indicator_of_notMem (show t∉Ioi (0:ℝ) from ht)]
    simp [H,ht]

theorem inverse_interval_lintegral {l u:ℝ} (hl:0<l) (hu:l≤u) :
    (∫⁻x in Ioo l u,ENNReal.ofReal ((x:ℝ)⁻¹))=
      ENNReal.ofReal (Real.log (u/l)) := by
  have hcon : ContinuousOn (fun x:ℝ=>x⁻¹) (Icc l u) :=
    continuousOn_id.inv₀ (fun x hx=>(hl.trans_le hx.1).ne')
  have hi : IntegrableOn (fun x:ℝ=>x⁻¹) (Icc l u) volume := hcon.integrableOn_Icc
  rw [Measure.restrict_congr_set Ioo_ae_eq_Icc,
    ←ofReal_integral_eq_lintegral_ofReal hi]
  · rw [integral_Icc_eq_integral_Ioc,←intervalIntegral.integral_of_le hu,
      integral_inv_of_pos hl (hl.trans_le hu)]
  · filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
    exact inv_nonneg.mpr (hl.le.trans hx.1)

def rectangleDensity (a b t:ℝ) : ℝ≥0∞ :=
  if 0<t ∧ t<a*b then ENNReal.ofReal (Real.log (a*b/t)) else 0

theorem rectangleDensity_section {a b t:ℝ} (hb:0<b) (ht:0<t) :
    (∫⁻x in Ioo (t/b) a,ENNReal.ofReal (x⁻¹))=rectangleDensity a b t := by
  by_cases htop:t<a*b
  · rw [rectangleDensity,if_pos ⟨ht,htop⟩,
      inverse_interval_lintegral (div_pos ht hb) ((div_lt_iff₀ hb).mpr htop).le]
    congr 1
    congr 1
    field_simp
  · have he : a≤t/b := (le_div_iff₀ hb).mpr (le_of_not_gt htop)
    simp [Ioo_eq_empty_of_le he,rectangleDensity,htop]

/-- Exact positive-rectangle product law against every nonnegative
measurable test.  This is the mixed-sign scalar density after reflection. -/
theorem rectangle_product_density {a b:ℝ} (hb:0<b)
    (F:ℝ→ℝ≥0∞) (hF:Measurable F) :
    (∫⁻x in Ioo 0 a,∫⁻y in Ioo 0 b,F (x*y))=
      ∫⁻t:ℝ,F t*rectangleDensity a b t := by
  rw [rectangle_product_lintegral hb F hF,←lintegral_indicator measurableSet_Ioi]
  apply lintegral_congr
  intro t
  by_cases ht:0<t
  · rw [Set.indicator_of_mem (show t∈Ioi (0:ℝ) from ht),
      rectangleDensity_section hb ht]
  · simp [rectangleDensity,ht]

end
end Resonance.CornerProductDensity
