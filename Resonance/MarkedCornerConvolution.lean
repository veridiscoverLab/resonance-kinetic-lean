import Resonance.MarkedAxisDomination

/-! The bounded marked axis remains in the complete original three-axis
zero-energy convolution. Enlarging one actual axis pays its entire mass
with the same sharp corner scale, uniformly in the other two deficits. -/
open Real Set MeasureTheory
open scoped ENNReal
namespace Resonance.MarkedCornerConvolution
noncomputable section
open AxisProductDensity CornerDensityBounds CornerZeroBounds CornerLogKernels
open CornerConvolution CornerConvolutionSigns CornerConvolutionBounds MarkedAxisDomination

theorem tripleZero_mono_first_ae {a a' : ℝ→ℝ≥0∞} (b c : ℝ→ℝ≥0∞)
    (ha : a≤ᵐ[(volume:Measure ℝ)]a') : tripleZero a b c≤tripleZero a' b c := by
  apply lintegral_mono_ae
  filter_upwards [ha] with s hs
  exact lintegral_mono (fun _=>mul_le_mul' (mul_le_mul' hs le_rfl) le_rfl)

theorem scaled_original_first (C : ℝ≥0∞) (d0 d1 d2 : ℝ) :
    tripleZero (fun s=>C*axisDensity d0 s) (axisDensity d1) (axisDensity d2)=
      C*sumDensity ![d0,d1,d2] 0 := by
  unfold tripleZero sumDensity
  simp only [Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,zero_sub]
  have hinner (s : ℝ) : (∫⁻t:ℝ,(C*axisDensity d0 s)*axisDensity d1 t*axisDensity d2 (-s-t))=
      C*(∫⁻t:ℝ,axisDensity d0 s*axisDensity d1 t*axisDensity d2 (-s-t)) := by
    simp only [mul_assoc]
    exact lintegral_const_mul _ (by
      have := axisDensity_measurable d1
      have := axisDensity_measurable d2
      fun_prop)
  simp_rw [hinner]
  exact lintegral_const_mul _ (by
    have hh : Measurable (fun p:ℝ×ℝ=>axisDensity d0 p.1*axisDensity d1 p.2*
        axisDensity d2 (-p.1-p.2)) := by
      have := axisDensity_measurable d0
      have := axisDensity_measurable d1
      have := axisDensity_measurable d2
      fun_prop
    exact hh.lintegral_prod_right')

theorem enlarged_log_bound {e : ℝ} (he : 0<e) (he1 : 8*e≤1) :
    logSize (8*e)≤logSize e := by
  rw [logSize_eq (by positivity) he1,logSize_eq he (by linarith)]
  have hl := Real.log_le_log he (by linarith:e≤8*e)
  linarith

theorem bounded_marked_convolution {e d1 d2 : ℝ} (he : 0<e)
    (he1 : e≤(1:ℝ)/4096) (h10 : 0≤d1) (h1e : d1≤e)
    (h20 : 0≤d2) (h2e : d2≤e) (B : ℝ≥0∞) (a : ℝ→ℝ≥0∞)
    (hb : ∀t,a t≤B) (hs : ∀t,2*e < |t| → a t=0) :
    tripleZero a (axisDensity d1) (axisDensity d2)≤
      (64*(B/ENNReal.ofReal (Real.log 2))*upperCoefficient)*
        (ENNReal.ofReal e)^2*(ENNReal.ofReal (logSize e))^2 := by
  have hd := bounded_marked_axis_domination he he1 B a hb hs
  have hfirst := tripleZero_mono_first_ae (axisDensity d1) (axisDensity d2) hd
  rw [scaled_original_first] at hfirst
  have hnonneg : ∀i:Fin 3,0≤(![8*e,d1,d2] i) := by
    intro i; fin_cases i
    · change 0≤8*e
      positivity
    · exact h10
    · exact h20
  have hbound : ∀i:Fin 3,(![8*e,d1,d2] i)≤8*e := by
    intro i; fin_cases i
    · exact le_rfl
    · change d1≤8*e
      linarith
    · change d2≤8*e
      linarith
  have hone : ∀i:Fin 3,(![8*e,d1,d2] i)≤1 := fun i=>(hbound i).trans (by linarith)
  have hsum := sumDensity_zero_upper ![8*e,d1,d2] hnonneg hbound hone (by positivity:0<8*e)
  have hlog : ENNReal.ofReal (logSize (8*e))≤ENNReal.ofReal (logSize e) :=
    ENNReal.ofReal_le_ofReal (enlarged_log_bound he (by linarith))
  apply hfirst.trans
  calc
    _ ≤ (B/ENNReal.ofReal (Real.log 2))*(upperCoefficient*(ENNReal.ofReal (8*e))^2*
        (ENNReal.ofReal (logSize (8*e)))^2) := mul_le_mul_right hsum _
    _ ≤ (B/ENNReal.ofReal (Real.log 2))*(upperCoefficient*(ENNReal.ofReal (8*e))^2*
        (ENNReal.ofReal (logSize e))^2) := by gcongr
    _ = _ := by rw [ENNReal.ofReal_mul (by norm_num:(0:ℝ)≤8)]; norm_num; ring

end
end Resonance.MarkedCornerConvolution
