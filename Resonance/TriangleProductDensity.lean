import Resonance.CornerProductDensity

open Real Set MeasureTheory
open scoped ENNReal Topology
namespace Resonance.TriangleProductDensity
noncomputable section
set_option maxHeartbeats 600000
open Resonance.CornerProductCoordinates Resonance.CornerProductDensity

def triangleDensity (b t:ℝ) : ℝ≥0∞ :=
  if 0<t ∧ t<b^2/4 then
    ENNReal.ofReal (Real.log ((b+Real.sqrt (b^2-4*t))^2/(4*t))) else 0

theorem triangle_product_section_lintegral {b t:ℝ} (hb:0<b) (ht:0<t)
    (hne:t≠b^2/4) :
    (∫⁻x in Ioi (0:ℝ),if x+t/x≤b then ENNReal.ofReal (x⁻¹) else 0)=
      triangleDensity b t := by
  by_cases htop:t<b^2/4
  · obtain ⟨hl,hlu,hs,hp⟩ := product_roots hb ht htop
    have he : (∫⁻x in Ioi (0:ℝ),if x+t/x≤b then ENNReal.ofReal (x⁻¹) else 0)=
        ∫⁻x in Icc (lowerRoot b t) (upperRoot b t),ENNReal.ofReal (x⁻¹) := by
      have hsub : Icc (lowerRoot b t) (upperRoot b t)⊆Ioi (0:ℝ) :=
        fun x hx=>hl.trans_le hx.1
      rw [←Set.inter_eq_left.mpr hsub,←Measure.restrict_restrict measurableSet_Icc,
        ←lintegral_indicator measurableSet_Icc]
      apply lintegral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      simp only [positive_product_section hb ht htop hx,Set.indicator_apply]
    rw [he,←Measure.restrict_congr_set Ioo_ae_eq_Icc,
      inverse_interval_lintegral hl hlu.le,triangleDensity,if_pos ⟨ht,htop⟩]
    congr 1
    congr 1
    calc
      upperRoot b t/lowerRoot b t=(upperRoot b t)^2/t := by
        apply (div_eq_div_iff hl.ne' ht.ne').mpr
        nlinarith [congrArg (fun z:ℝ=>upperRoot b t*z) hp]
      _ = _ := by dsimp [upperRoot]; ring
  · have hgt : b^2/4<t := lt_of_le_of_ne (le_of_not_gt htop) hne.symm
    rw [triangleDensity,if_neg (not_and.mpr (fun _=>htop))]
    suffices hz : (fun x:ℝ=>if x+t/x≤b then ENNReal.ofReal (x⁻¹) else 0)
        =ᵐ[(volume:Measure ℝ).restrict (Ioi 0)] 0 by
      simpa using lintegral_congr_ae hz
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hx0 : 0<x := hx
    have hbad : ¬x+t/x≤b := by
      intro h
      have hm := (mul_le_mul_iff_right₀ hx0).mpr h
      have hpol : x^2-b*x+t≤0 := by
        have he : x*(x+t/x)=x^2+t := by field_simp
        rw [he] at hm
        nlinarith
      nlinarith [sq_nonneg (2*x-b)]
    exact if_neg hbad

/-- The whole same-sign triangle is pushed through the same product
coordinate map.  Its only exceptional scalar level is a Lebesgue-null
double-root level; it is not deleted from the original source integral. -/
theorem triangle_product_density {b:ℝ} (hb:0<b)
    (F:ℝ→ℝ≥0∞) (hF:Measurable F) :
    (∫⁻x in Ioi (0:ℝ),∫⁻y in Ioi (0:ℝ),if x+y≤b then F (x*y) else 0)=
      ∫⁻t:ℝ,F t*triangleDensity b t := by
  let H : ℝ×ℝ→ℝ≥0∞ := fun p=>
    if 0<p.2 ∧ p.1+p.2/p.1≤b then F p.2 else 0
  have hH : Measurable H := by
    apply Measurable.ite
    · exact (measurableSet_lt measurable_const measurable_snd).inter
        (measurableSet_le (measurable_fst.add (measurable_snd.div measurable_fst)) measurable_const)
    · exact hF.comp measurable_snd
    · exact measurable_const
  have hc := product_coordinate_lintegral H hH
  have hleft : (∫⁻x in Ioi (0:ℝ),∫⁻y:ℝ,H (x,x*y))=
      ∫⁻x in Ioi (0:ℝ),∫⁻y in Ioi (0:ℝ),if x+y≤b then F (x*y) else 0 := by
    apply lintegral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hx0 : 0<x := hx
    rw [←lintegral_indicator measurableSet_Ioi]
    apply lintegral_congr
    intro y
    have he : x*y/x=y := by field_simp
    simp only [H,he,mul_pos_iff_of_pos_left hx0,Set.indicator_apply,mem_Ioi]
    by_cases hy:0<y <;> by_cases hs:x+y≤b <;> simp [hy,hs]
  rw [hleft] at hc
  rw [hc]
  have hK : Measurable (fun p:ℝ×ℝ=>ENNReal.ofReal (p.1⁻¹)*H p) := by fun_prop
  rw [lintegral_lintegral_swap hK.aemeasurable]
  apply lintegral_congr_ae
  have hae : ∀ᵐt:ℝ,t≠b^2/4 := by simp [ae_iff]
  filter_upwards [hae] with t hne
  by_cases ht:0<t
  · have he : (∫⁻x in Ioi (0:ℝ),ENNReal.ofReal (x⁻¹)*H (x,t))=
        F t*(∫⁻x in Ioi (0:ℝ),if x+t/x≤b then ENNReal.ofReal (x⁻¹) else 0) := by
      rw [←lintegral_const_mul]
      · apply lintegral_congr
        intro x
        simp only [H,ht,true_and]
        split_ifs <;> simp [mul_comm]
      · apply Measurable.ite
        · exact measurableSet_le (measurable_id.add (measurable_const.div measurable_id)) measurable_const
        · fun_prop
        · exact measurable_const
    rw [he,triangle_product_section_lintegral hb ht hne]
  · simp [H,ht,triangleDensity]

theorem triangleDensity_zero (t:ℝ) : triangleDensity 0 t=0 := by
  have h : ¬(0<t ∧ t<(0:ℝ)^2/4) := by
    rintro ⟨h1,h2⟩
    norm_num at h2
    exact (lt_asymm h1 h2)
  exact if_neg h

theorem triangle_product_density_nonnegative {b:ℝ} (hb:0≤b)
    (F:ℝ→ℝ≥0∞) (hF:Measurable F) :
    (∫⁻x in Ioi (0:ℝ),∫⁻y in Ioi (0:ℝ),if x+y≤b then F (x*y) else 0)=
      ∫⁻t:ℝ,F t*triangleDensity b t := by
  rcases hb.eq_or_lt with h0|hpos
  · subst b
    simp only [triangleDensity_zero,mul_zero,lintegral_zero]
    suffices hz : (fun x:ℝ=>∫⁻y in Ioi (0:ℝ),if x+y≤0 then F (x*y) else 0)
        =ᵐ[(volume:Measure ℝ).restrict (Ioi 0)] 0 by
      simpa using lintegral_congr_ae hz
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    suffices hyz : (fun y:ℝ=>if x+y≤0 then F (x*y) else 0)
        =ᵐ[(volume:Measure ℝ).restrict (Ioi 0)] 0 by
      simpa using lintegral_congr_ae hyz
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
    exact if_neg (by have hx0 : 0<x := hx; have hy0 : 0<y := hy; linarith)
  · exact triangle_product_density hpos F hF

end
end Resonance.TriangleProductDensity
