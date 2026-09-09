import Resonance.MarkedPhysicalScaling

/-! Relative fixed-output mass bounds for an actual continuous axis
mark. The constant is independent of all three corner deficits and of
the physical cube size. -/
open Real Set MeasureTheory
open scoped ENNReal
namespace Resonance.MarkedRelativeMass
noncomputable section
open PlaneCoarea CubeAxisCoordinates MarkedProductDensity MarkedProductBounds
open MarkedDensityContinuity MarkedConvolutionSupport MarkedPhysicalScaling
open CornerConvolution CornerZeroBounds CornerLogKernels
set_option maxHeartbeats 1200000

def relativeConstant : ℝ := 256*upperCoefficient.toReal/(Real.log 2*lowerConstant)

theorem relativeConstant_nonneg : 0≤relativeConstant := by
  unfold relativeConstant
  exact div_nonneg (by positivity) (mul_nonneg (Real.log_nonneg (by norm_num)) lowerConstant_pos.le)

theorem actual_marked_sum_real_bound {d : Fin 3→ℝ} {e B : ℝ}
    (he : 0<e) (he1 : e≤(1:ℝ)/4096) (hd0 : ∀i,0≤d i) (hde : ∀i,d i≤e)
    (hB : 0≤B) {w : ℝ×ℝ→ℝ} (hb : ∀p,w p≤1)
    (hbound : ∀t,productDensity (markedWeight (d 0) (fun p=>ENNReal.ofReal (w p))) t≤ENNReal.ofReal B) :
    (markedSum (productDensity (markedWeight (d 0) (fun p=>ENNReal.ofReal (w p))))
      (d 1) (d 2) 0).toReal≤
      64*(B/Real.log 2)*upperCoefficient.toReal*e^2*(logSize e)^2 := by
  have hlog : 0<Real.log (2:ℝ) := Real.log_pos (by norm_num)
  have hu := original_marked_convolution_bound he he1 (hd0 0) (hde 0) (hd0 1) (hde 1)
    (hd0 2) (hde 2) (ENNReal.ofReal B) _ hbound
    (marked_density_le_original (hd0 0) (lt_of_le_of_lt (hde 0) (by linarith)) _
      (fun p=>ENNReal.ofReal_le_one.mpr (hb p)))
  have hc : ((64*(ENNReal.ofReal B/ENNReal.ofReal (Real.log 2))*upperCoefficient)*
      (ENNReal.ofReal e)^2*(ENNReal.ofReal (logSize e))^2)≠∞ := by
    have hden : ENNReal.ofReal (Real.log 2)≠0 := (ENNReal.ofReal_pos.mpr hlog).ne'
    have hdiv : ENNReal.ofReal B/ENNReal.ofReal (Real.log 2)≠∞ :=
      ENNReal.div_ne_top ENNReal.ofReal_ne_top hden
    exact (ENNReal.mul_lt_top (ENNReal.mul_lt_top (ENNReal.mul_lt_top
      (ENNReal.mul_lt_top (by norm_num) (lt_top_iff_ne_top.mpr hdiv)) upperCoefficient_finite)
      (ENNReal.pow_lt_top ENNReal.ofReal_lt_top)) (ENNReal.pow_lt_top ENNReal.ofReal_lt_top)).ne
  have ht := ENNReal.toReal_mono hc hu
  simpa only [markedSum,CornerConvolutionSigns.tripleZero,zero_sub,
    ENNReal.toReal_mul,ENNReal.toReal_div,ENNReal.toReal_pow,ENNReal.toReal_ofNat,
    ENNReal.toReal_ofReal hB,ENNReal.toReal_ofReal hlog.le,
    ENNReal.toReal_ofReal he.le,ENNReal.toReal_ofReal (logSize_nonneg e)] using ht

theorem actual_marked_sum_relative {d : Fin 3→ℝ} {e B : ℝ}
    (he : 0<e) (he1 : e≤(1:ℝ)/4096) (hd0 : ∀i,0≤d i) (hde : ∀i,d i≤e)
    (hmax : ∃i,d i=e) (hB : 0≤B) {w : ℝ×ℝ→ℝ} (hb : ∀p,w p≤1)
    (hbound : ∀t,productDensity (markedWeight (d 0) (fun p=>ENNReal.ofReal (w p))) t≤ENNReal.ofReal B) :
    (markedSum (productDensity (markedWeight (d 0) (fun p=>ENNReal.ofReal (w p))))
      (d 1) (d 2) 0).toReal≤relativeConstant*B*(sumDensity d 0).toReal := by
  have hm := actual_marked_sum_real_bound he he1 hd0 hde hB hb hbound
  have hl := (sumDensity_zero_two_sided d hd0 hde hmax he (by linarith)).1
  have hlog := logSize_corner_bound he (by linarith)
  have hs : (logSize e)^2≤4*(Real.log (1/e))^2 := by nlinarith [logSize_nonneg e]
  have hp : 0≤64*(B/Real.log 2)*upperCoefficient.toReal*e^2 := by
    exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num)
      (div_nonneg hB (Real.log_nonneg (by norm_num)))) ENNReal.toReal_nonneg) (sq_nonneg e)
  calc
    _ ≤ 64*(B/Real.log 2)*upperCoefficient.toReal*e^2*(logSize e)^2 := hm
    _ ≤ 64*(B/Real.log 2)*upperCoefficient.toReal*e^2*(4*(Real.log (1/e))^2) :=
      mul_le_mul_of_nonneg_left hs hp
    _ = relativeConstant*B*(lowerConstant*e^2*(Real.log (1/e))^2) := by
      unfold relativeConstant
      field_simp [lowerConstant_pos.ne', (Real.log_pos (by norm_num : (1:ℝ)<2)).ne']
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hl (mul_nonneg relativeConstant_nonneg hB)

theorem actual_marked_mass_relative {L : ℝ} (hL : 0<L) {d : Fin 3→ℝ} {e B : ℝ}
    (he : 0<e) (he1 : e≤(1:ℝ)/4096) (hd0 : ∀i,0≤d i) (hde : ∀i,d i≤e)
    (hmax : ∃i,d i=e) (hB : 0≤B) {w : ℝ×ℝ→ℝ}
    (hw : Continuous w) (hp : ∀p,0≤w p) (hb : ∀p,w p≤1)
    (hbound : ∀t,productDensity (markedWeight (d 0) (fun p=>ENNReal.ofReal (w p))) t≤ENNReal.ofReal B) :
    FiberContinuity.fiberReadout (L/2) (scaledMark L w) (L•normalizedOutput d)≤
      relativeConstant*B*CollisionFrequency.geometricFrequency (L/2) (L•normalizedOutput d) := by
  have hd1 : ∀i,d i<1 := fun i=>lt_of_le_of_lt (hde i) (by linarith)
  have hm := congrArg ENNReal.toReal (original_scaled_marked_frequency hL hd0 hd1 hw hp hb)
  have hn := congrArg ENNReal.toReal
    (CollisionFrequencyConvolution.original_frequency_eq_convolution hL hd0 hd1)
  have hp0 : 0≤FiberContinuity.fiberReadout (L/2) (scaledMark L w) (L•normalizedOutput d) :=
    integral_nonneg (fun q=>hp _)
  simp only [ENNReal.toReal_ofReal hp0,ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (by positivity : 0≤L^4/2)] at hm
  simp only [ENNReal.toReal_ofReal (CollisionFrequency.geometricFrequency_nonnegative _ _),
    ENNReal.toReal_mul,ENNReal.toReal_ofReal (by positivity : 0≤L^4/2)] at hn
  rw [hm,hn]
  exact (mul_le_mul_of_nonneg_left (actual_marked_sum_relative he he1 hd0 hde hmax hB hb hbound)
    (by positivity : 0≤L^4/2)).trans_eq (by ring)

theorem continuous_strip_density_bound (d : ℝ) {l a b : ℝ} (hl : 0<l)
    (hfar : ∀x∈Icc a b,l≤|x|) {w : ℝ×ℝ→ℝ}
    (hb : ∀p,w p≤1) (hs : ∀p,p.1∉Icc a b→w p=0) (t : ℝ) :
    productDensity (markedWeight d (fun p=>ENNReal.ofReal (w p))) t≤
      ENNReal.ofReal ((b-a)/l) := by
  have hmono : ∀p,markedWeight d (fun p=>ENNReal.ofReal (w p)) p≤
      markedWeight d (fun p=>(Icc a b).indicator (fun _=>1) p.1) p := by
    intro p
    by_cases hd:p∈CornerProductCoordinates.axisDomain d
    · simp only [markedWeight,indicator_of_mem hd]
      by_cases hp:p.1∈Icc a b
      · rw [indicator_of_mem hp]
        exact ENNReal.ofReal_le_one.mpr (hb p)
      · rw [indicator_of_notMem hp,hs p hp,ENNReal.ofReal_zero]
    · simp only [markedWeight,indicator_of_notMem hd,le_refl]
  have h := (productDensity_mono hmono t).trans (marked_far_strip_bound d hl hfar t)
  convert h using 1
  rw [←ENNReal.ofReal_mul (inv_nonneg.mpr hl.le)]
  congr 1
  exact div_eq_inv_mul _ _

theorem actual_far_strip_mass {L : ℝ} (hL : 0<L) {d : Fin 3→ℝ} {e l a b : ℝ}
    (he : 0<e) (he1 : e≤(1:ℝ)/4096) (hd0 : ∀i,0≤d i) (hde : ∀i,d i≤e)
    (hmax : ∃i,d i=e) (hl : 0<l) (hab : a≤b) (hfar : ∀x∈Icc a b,l≤|x|)
    {w : ℝ×ℝ→ℝ} (hw : Continuous w) (hp : ∀p,0≤w p) (hb : ∀p,w p≤1)
    (hs : ∀p,p.1∉Icc a b→w p=0) :
    FiberContinuity.fiberReadout (L/2) (scaledMark L w) (L•normalizedOutput d)≤
      relativeConstant*((b-a)/l)*CollisionFrequency.geometricFrequency (L/2) (L•normalizedOutput d) :=
  actual_marked_mass_relative hL he he1 hd0 hde hmax
    (div_nonneg (sub_nonneg.mpr hab) hl.le) hw hp hb
    (continuous_strip_density_bound (d 0) hl hfar hb hs)

end
end Resonance.MarkedRelativeMass
