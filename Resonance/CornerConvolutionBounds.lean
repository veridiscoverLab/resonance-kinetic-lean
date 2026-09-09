import Resonance.CornerConvolution
import Resonance.AxisDensityIntegrability

/-! Uniform estimates for the complete zero-energy convolution of the
three proved original axis densities. -/
open Real Set MeasureTheory Filter
open scoped ENNReal Topology
namespace Resonance.CornerConvolutionBounds
noncomputable section
set_option maxHeartbeats 600000
open Resonance.CornerConvolution Resonance.AxisProductDensity
open Resonance.CornerProductDensity Resonance.TriangleProductDensity
open Resonance.CornerDensityBounds Resonance.CornerLogKernels Resonance.AxisDensityIntegrability

def positiveDensity (d t:ℝ) : ℝ≥0∞ := triangleDensity d t+triangleDensity (1-d) t
def negativeDensity (d s:ℝ) : ℝ≥0∞ := 2*rectangleDensity d (1-d) s
def positiveConvolution (d₁ d₂ s:ℝ) : ℝ≥0∞ :=
  ∫⁻t in Ioo 0 s,positiveDensity d₁ t*positiveDensity d₂ (s-t)

theorem positiveDensity_measurable (d:ℝ) : Measurable (positiveDensity d) :=
  (triangleDensity_measurable d).add (triangleDensity_measurable (1-d))
theorem negativeDensity_measurable (d:ℝ) : Measurable (negativeDensity d) :=
  measurable_const.mul (rectangleDensity_measurable d (1-d))

theorem positive_scaled_upper {d s u:ℝ} (hd0:0≤d) (hd1:d≤1) (hs:0<s) (hu:0<u) :
    positiveDensity d (s*u)≤2*ENNReal.ofReal (logSize s)*ENNReal.ofReal (logSize u) := by
  have hb := axisDensity_positive_bound hd0 hd1 (mul_pos hs hu)
  rw [axis_density_positive (mul_pos hs hu)] at hb
  change positiveDensity d (s*u)≤_ at hb
  calc
    _ ≤ 2*ENNReal.ofReal (logSize (s*u)) := hb
    _ ≤ 2*ENNReal.ofReal (logSize s*logSize u) :=
      mul_le_mul_right (ENNReal.ofReal_le_ofReal (logSize_mul_le s u hs.ne' hu.ne')) 2
    _ = _ := by rw [ENNReal.ofReal_mul (logSize_nonneg s)]; ring

theorem positive_convolution_upper {d₁ d₂ s:ℝ}
    (h10:0≤d₁) (h11:d₁≤1) (h20:0≤d₂) (h21:d₂≤1) (hs:0<s) :
    positiveConvolution d₁ d₂ s≤
      8*ENNReal.ofReal s*(ENNReal.ofReal (logSize s))^2*logMoment 2 := by
  unfold positiveConvolution
  have hscale := scale_unit_lintegral hs (fun t=>positiveDensity d₁ t*positiveDensity d₂ (s-t))
    ((positiveDensity_measurable d₁).mul
      ((positiveDensity_measurable d₂).comp (measurable_const.sub measurable_id)))
  rw [hscale]
  have hM : Measurable (fun u:ℝ=>ENNReal.ofReal ((logSize u)^2)+
      ENNReal.ofReal ((logSize (1-u))^2)) := by unfold logSize; fun_prop
  have hpoint : ∀ᵐ u ∂(volume:Measure ℝ).restrict (Ioo 0 1),
      positiveDensity d₁ (s*u)*positiveDensity d₂ (s-s*u)≤
      (4*(ENNReal.ofReal (logSize s))^2)*
        (ENNReal.ofReal ((logSize u)^2)+ENNReal.ofReal ((logSize (1-u))^2)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with u hu
    have hw : 0<1-u := by linarith [hu.2]
    have h1 := positive_scaled_upper h10 h11 hs hu.1
    have h2 := positive_scaled_upper h20 h21 hs hw
    have he : s-s*u=s*(1-u) := by ring
    rw [he]
    have hquad : logSize u*logSize (1-u)≤(logSize u)^2+(logSize (1-u))^2 := by
      nlinarith [sq_nonneg (logSize u-logSize (1-u))]
    have hqe : ENNReal.ofReal (logSize u)*ENNReal.ofReal (logSize (1-u))≤
        ENNReal.ofReal ((logSize u)^2)+ENNReal.ofReal ((logSize (1-u))^2) := by
      rw [←ENNReal.ofReal_mul (logSize_nonneg u),
        ←ENNReal.ofReal_add (sq_nonneg _) (sq_nonneg _)]
      exact ENNReal.ofReal_le_ofReal hquad
    calc
      _ ≤ (2*ENNReal.ofReal (logSize s)*ENNReal.ofReal (logSize u))*
          (2*ENNReal.ofReal (logSize s)*ENNReal.ofReal (logSize (1-u))) := mul_le_mul' h1 h2
      _ = (4*(ENNReal.ofReal (logSize s))^2)*
          (ENNReal.ofReal (logSize u)*ENNReal.ofReal (logSize (1-u))) := by ring
      _ ≤ _ := mul_le_mul_right hqe _
  have houter := lintegral_mono_ae hpoint
  have hsum : (∫⁻u in Ioo (0:ℝ) 1,ENNReal.ofReal ((logSize u)^2)+
      ENNReal.ofReal ((logSize (1-u))^2))=logMoment 2+logMoment 2 := by
    rw [lintegral_add_left (by unfold logSize; fun_prop),
      reflect_unit_lintegral (fun u=>ENNReal.ofReal ((logSize u)^2))]
    rfl
  have hext : (∫⁻u in Ioo (0:ℝ) 1,(4*(ENNReal.ofReal (logSize s))^2)*
      (ENNReal.ofReal ((logSize u)^2)+ENNReal.ofReal ((logSize (1-u))^2)))=
      (4*(ENNReal.ofReal (logSize s))^2)*(logMoment 2+logMoment 2) := by
    exact (lintegral_const_mul _ hM).trans (congrArg _ hsum)
  rw [hext] at houter
  exact (mul_le_mul_right houter (ENNReal.ofReal s)).trans_eq (by ring)

theorem positiveConvolution_measurable (d₁ d₂:ℝ) : Measurable (positiveConvolution d₁ d₂) := by
  have hm : Measurable (fun p:ℝ×ℝ=>if 0<p.2 ∧ p.2<p.1 then
      positiveDensity d₁ p.2*positiveDensity d₂ (p.1-p.2) else 0) := by
    apply Measurable.ite
    · exact (measurableSet_lt measurable_const measurable_snd).inter
        (measurableSet_lt measurable_snd measurable_fst)
    · exact ((positiveDensity_measurable d₁).comp measurable_snd).mul
        ((positiveDensity_measurable d₂).comp (measurable_fst.sub measurable_snd))
    · exact measurable_const
  have he (s:ℝ) : (∫⁻t:ℝ,if 0<t ∧ t<s then
      positiveDensity d₁ t*positiveDensity d₂ (s-t) else 0)=positiveConvolution d₁ d₂ s := by
    simpa only [Set.indicator_apply,mem_Ioo] using
      (lintegral_indicator (μ:=(volume:Measure ℝ))
        (show MeasurableSet (Ioo (0:ℝ) s) from measurableSet_Ioo)
        (fun t=>positiveDensity d₁ t*positiveDensity d₂ (s-t)))
  have hm' : Measurable (fun s:ℝ=>∫⁻t:ℝ,if 0<t ∧ t<s then
      positiveDensity d₁ t*positiveDensity d₂ (s-t) else 0) := hm.lintegral_prod_right'
  simpa only [he] using hm'

def oneNegative (dj di dl:ℝ) : ℝ≥0∞ :=
  ∫⁻s in Ioi (0:ℝ),negativeDensity dj s*positiveConvolution di dl s

theorem negative_scaled_upper {d e r:ℝ} (hd0:0≤d) (hde:d≤e) (he:0<e) (hr:0<r) :
    negativeDensity d (e*r)≤2*ENNReal.ofReal (logSize r) := by
  have hb := rectangle_density_upper hd0 hde (mul_pos he hr)
  have heq : e/(e*r)=1/r := by field_simp
  rw [heq] at hb
  have hl : Real.log (1/r)≤logSize r := by
    rw [one_div,Real.log_inv]
    dsimp [logSize]
    linarith [neg_le_abs (Real.log r)]
  exact mul_le_mul_right (hb.trans (ENNReal.ofReal_le_ofReal hl)) 2

theorem one_negative_upper {dj di dl e:ℝ}
    (hj0:0≤dj) (hje:dj≤e) (hi0:0≤di) (hi1:di≤1)
    (hl0:0≤dl) (hl1:dl≤1) (he:0<e) :
    oneNegative dj di dl≤16*(ENNReal.ofReal e)^2*(ENNReal.ofReal (logSize e))^2*
      logMoment 2*logMoment 3 := by
  have hF : Measurable (fun s=>negativeDensity dj s*positiveConvolution di dl s) :=
    (negativeDensity_measurable dj).mul (positiveConvolution_measurable di dl)
  have hrestrict : oneNegative dj di dl=
      ∫⁻s in Ioo 0 e,negativeDensity dj s*positiveConvolution di dl s := by
    rw [CornerProductDensity.lintegral_Ioo_split]
    unfold oneNegative
    apply lintegral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s _hs
    by_cases hse:s<e
    · rw [if_pos hse]
    · rw [if_neg hse,negativeDensity,rectangle_density_zero_of_large hj0 hje (le_of_not_gt hse)]
      simp
  rw [hrestrict,scale_unit_lintegral he _ hF]
  have hpoint : ∀ᵐ r ∂(volume:Measure ℝ).restrict (Ioo 0 1),
      negativeDensity dj (e*r)*positiveConvolution di dl (e*r)≤
      (16*ENNReal.ofReal e*(ENNReal.ofReal (logSize e))^2*logMoment 2)*
        ENNReal.ofReal ((logSize r)^3) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
    have hn := negative_scaled_upper hj0 hje he hr.1
    have hp := positive_convolution_upper hi0 hi1 hl0 hl1 (mul_pos he hr.1)
    have hm : ENNReal.ofReal (logSize (e*r))≤
        ENNReal.ofReal (logSize e)*ENNReal.ofReal (logSize r) := by
      rw [←ENNReal.ofReal_mul (logSize_nonneg e)]
      exact ENNReal.ofReal_le_ofReal (logSize_mul_le e r he.ne' hr.1.ne')
    have hr1 : ENNReal.ofReal r≤1 := by exact_mod_cast hr.2.le
    calc
      _ ≤ (2*ENNReal.ofReal (logSize r))*
          (8*ENNReal.ofReal (e*r)*(ENNReal.ofReal (logSize (e*r)))^2*logMoment 2) := mul_le_mul' hn hp
      _ ≤ (2*ENNReal.ofReal (logSize r))*
          (8*(ENNReal.ofReal e*1)*
            (ENNReal.ofReal (logSize e)*ENNReal.ofReal (logSize r))^2*logMoment 2) := by
        rw [ENNReal.ofReal_mul he.le]
        gcongr
      _ = _ := by rw [ENNReal.ofReal_pow (logSize_nonneg r)]; ring
  have hI := lintegral_mono_ae hpoint
  have hpow : Measurable (fun r:ℝ=>ENNReal.ofReal ((logSize r)^3)) := by unfold logSize; fun_prop
  have hint : (∫⁻r in Ioo (0:ℝ) 1,
      (16*ENNReal.ofReal e*(ENNReal.ofReal (logSize e))^2*logMoment 2)*ENNReal.ofReal ((logSize r)^3))=
      (16*ENNReal.ofReal e*(ENNReal.ofReal (logSize e))^2*logMoment 2)*logMoment 3 :=
    lintegral_const_mul _ hpow
  rw [hint] at hI
  exact (mul_le_mul_right hI (ENNReal.ofReal e)).trans_eq (by ring)

theorem positive_sum_scaled_upper {d e r q:ℝ} (hd0:0≤d) (hd1:d≤1)
    (he:0<e) (hr:0<r) (hq:0<q) :
    positiveDensity d (e*(r+q))≤
      2*ENNReal.ofReal (logSize e)*ENNReal.ofReal (logSize r) := by
  have hs : 0<e*(r+q) := mul_pos he (add_pos hr hq)
  have hlog : Real.log (1/(e*(r+q)))≤logSize e*logSize r := by
    have hh : 1/(e*(r+q))≤1/(e*r) :=
      one_div_le_one_div_of_le (mul_pos he hr) (by nlinarith)
    have ha : Real.log (1/(e*r))≤logSize (e*r) := by
      rw [one_div,Real.log_inv]
      dsimp [logSize]
      linarith [neg_le_abs (Real.log (e*r))]
    exact (Real.log_le_log (by positivity) hh).trans
      (ha.trans (logSize_mul_le e r he.ne' hr.ne'))
  have h1 := (triangle_density_upper hd0 hd1 hs).trans (ENNReal.ofReal_le_ofReal hlog)
  have h2 := (triangle_density_upper (by linarith:0≤1-d) (by linarith:1-d≤1) hs).trans
    (ENNReal.ofReal_le_ofReal hlog)
  exact (add_le_add h1 h2).trans_eq (by
    rw [ENNReal.ofReal_mul (logSize_nonneg e)]
    ring)

theorem negative_lintegral_restrict {d e:ℝ} (hd0:0≤d) (hde:d≤e)
    (F:ℝ→ℝ≥0∞) :
    (∫⁻s in Ioi (0:ℝ),negativeDensity d s*F s)=
      ∫⁻s in Ioo 0 e,negativeDensity d s*F s := by
  rw [CornerProductDensity.lintegral_Ioo_split]
  apply lintegral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with s _hs
  by_cases hse:s<e
  · rw [if_pos hse]
  · rw [if_neg hse,negativeDensity,rectangle_density_zero_of_large hd0 hde (le_of_not_gt hse)]
    simp

def twoNegative (di dl dj:ℝ) : ℝ≥0∞ :=
  ∫⁻u in Ioi (0:ℝ),negativeDensity di u*
    (∫⁻v in Ioi (0:ℝ),negativeDensity dl v*positiveDensity dj (u+v))

theorem two_negative_upper {di dl dj e:ℝ}
    (hi0:0≤di) (hie:di≤e) (hl0:0≤dl) (hle:dl≤e)
    (hj0:0≤dj) (hj1:dj≤1) (he:0<e) :
    twoNegative di dl dj≤8*(ENNReal.ofReal e)^2*ENNReal.ofReal (logSize e)*
      logMoment 2*logMoment 1 := by
  unfold twoNegative
  rw [negative_lintegral_restrict hi0 hie]
  simp_rw [negative_lintegral_restrict hl0 hle]
  have hM : Measurable (fun p:ℝ×ℝ=>negativeDensity dl p.2*positiveDensity dj (p.1+p.2)) :=
    ((negativeDensity_measurable dl).comp measurable_snd).mul
      ((positiveDensity_measurable dj).comp (measurable_fst.add measurable_snd))
  have hF : Measurable (fun u:ℝ=>negativeDensity di u*
      ∫⁻v in Ioo 0 e,negativeDensity dl v*positiveDensity dj (u+v)) :=
    (negativeDensity_measurable di).mul hM.lintegral_prod_right'
  rw [scale_unit_lintegral he _ hF]
  have hscale (u:ℝ) := scale_unit_lintegral he
    (fun v=>negativeDensity dl v*positiveDensity dj (u+v))
    ((negativeDensity_measurable dl).mul
      ((positiveDensity_measurable dj).comp (measurable_const.add measurable_id)))
  simp_rw [hscale]
  have hpoint : ∀ᵐ r ∂(volume:Measure ℝ).restrict (Ioo 0 1),
      negativeDensity di (e*r)*(ENNReal.ofReal e*
        ∫⁻q in Ioo 0 1,negativeDensity dl (e*q)*positiveDensity dj (e*r+e*q))≤
      (8*ENNReal.ofReal e*ENNReal.ofReal (logSize e)*logMoment 1)*
        ENNReal.ofReal ((logSize r)^2) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
    have hinner : (∫⁻q in Ioo (0:ℝ) 1,
        negativeDensity dl (e*q)*positiveDensity dj (e*r+e*q))≤
        (4*ENNReal.ofReal (logSize e)*ENNReal.ofReal (logSize r))*logMoment 1 := by
      have hp : ∀ᵐ q ∂(volume:Measure ℝ).restrict (Ioo 0 1),
          negativeDensity dl (e*q)*positiveDensity dj (e*r+e*q)≤
          (4*ENNReal.ofReal (logSize e)*ENNReal.ofReal (logSize r))*
            ENNReal.ofReal ((logSize q)^1) := by
        filter_upwards [ae_restrict_mem measurableSet_Ioo] with q hq
        have hn := negative_scaled_upper hl0 hle he hq.1
        have hg := positive_sum_scaled_upper hj0 hj1 he hr.1 hq.1
        rw [show e*(r+q)=e*r+e*q by ring] at hg
        exact (mul_le_mul' hn hg).trans_eq (by simp only [pow_one]; ring)
      exact (lintegral_mono_ae hp).trans_eq
        (lintegral_const_mul _ (by unfold logSize; fun_prop))
    have hn := negative_scaled_upper hi0 hie he hr.1
    exact (mul_le_mul' hn (mul_le_mul_right hinner (ENNReal.ofReal e))).trans_eq (by
      rw [ENNReal.ofReal_pow (logSize_nonneg r)]
      ring)
  have hout := lintegral_mono_ae hpoint
  have hC : (∫⁻r in Ioo (0:ℝ) 1,
      (8*ENNReal.ofReal e*ENNReal.ofReal (logSize e)*logMoment 1)*
        ENNReal.ofReal ((logSize r)^2))=
      (8*ENNReal.ofReal e*ENNReal.ofReal (logSize e)*logMoment 1)*logMoment 2 :=
    lintegral_const_mul _ (by unfold logSize; fun_prop)
  rw [hC] at hout
  exact (mul_le_mul_right hout (ENNReal.ofReal e)).trans_eq (by ring)

end
end Resonance.CornerConvolutionBounds
