import Resonance.MarkedCornerConvolution

/-! Exact marked product pushforward, retaining the original one-axis
flags. This supplies actual marked densities for the common collision
convolution rather than introducing a separate kernel model. -/
open Real Set MeasureTheory
open scoped ENNReal
namespace Resonance.MarkedProductDensity
noncomputable section
open CornerProductCoordinates AxisProductDensity
set_option maxHeartbeats 1000000

def productDensity (w : ℝ×ℝ→ℝ≥0∞) (t : ℝ) : ℝ≥0∞ :=
  ∫⁻x:ℝ,ENNReal.ofReal (|x⁻¹|)*w (x,t/x)

theorem productDensity_measurable {w : ℝ×ℝ→ℝ≥0∞} (hw : Measurable w) :
    Measurable (productDensity w) := by
  have hm : Measurable (fun p:ℝ×ℝ=>ENNReal.ofReal (|p.2⁻¹|)*w (p.2,p.1/p.2)) := by fun_prop
  exact hm.lintegral_prod_right'

theorem actual_product_pushforward {w : ℝ×ℝ→ℝ≥0∞} (hw : Measurable w)
    (F : ℝ→ℝ≥0∞) (hF : Measurable F) :
    (∫⁻x:ℝ,∫⁻y:ℝ,w (x,y)*F (x*y))=
      ∫⁻t:ℝ,F t*productDensity w t := by
  have hpoint : ∀ᵐ x ∂(volume:Measure ℝ),
      (∫⁻y:ℝ,w (x,y)*F (x*y))=
        ∫⁻t:ℝ,ENNReal.ofReal (|x⁻¹|)*(w (x,t/x)*F t) := by
    filter_upwards [(volume:Measure ℝ).ae_ne 0] with x hx
    let G : ℝ→ℝ≥0∞ := fun t=>w (x,t/x)*F t
    have hG : Measurable G := by dsimp [G]; fun_prop
    calc
      _ = ∫⁻y:ℝ,G (x*y) := by
        apply lintegral_congr
        intro y
        dsimp [G]
        rw [mul_div_cancel_left₀ y hx]
      _ = ∫⁻t:ℝ,G t∂Measure.map (fun y:ℝ=>x*y) volume :=
        (lintegral_map hG (measurable_const_mul x)).symm
      _ = _ := by
        rw [Real.map_volume_mul_left hx,lintegral_smul_measure,smul_eq_mul,
          ←lintegral_const_mul _ hG]
  rw [lintegral_congr_ae hpoint]
  have hm : Measurable (fun p:ℝ×ℝ=>ENNReal.ofReal (|p.1⁻¹|)*(w (p.1,p.2/p.1)*F p.2)) := by fun_prop
  rw [lintegral_lintegral_swap hm.aemeasurable]
  apply lintegral_congr
  intro t
  unfold productDensity
  rw [←lintegral_const_mul _ (by fun_prop : Measurable (fun x:ℝ=>ENNReal.ofReal (|x⁻¹|)*w (x,t/x)))]
  apply lintegral_congr
  intro x
  ring

def markedWeight (d : ℝ) (w : ℝ×ℝ→ℝ≥0∞) : ℝ×ℝ→ℝ≥0∞ :=
  (axisDomain d).indicator w

theorem markedWeight_measurable (d : ℝ) {w : ℝ×ℝ→ℝ≥0∞} (hw : Measurable w) :
    Measurable (markedWeight d w) := hw.indicator (axisDomain_measurable d)

theorem actual_marked_polygon_density (d : ℝ) {w : ℝ×ℝ→ℝ≥0∞}
    (hw : Measurable w) (F : ℝ→ℝ≥0∞) (hF : Measurable F) :
    (∫⁻p in axisDomain d,w p*F (p.1*p.2)∂((volume:Measure ℝ).prod volume))=
      ∫⁻t:ℝ,F t*productDensity (markedWeight d w) t := by
  rw [←lintegral_indicator (axisDomain_measurable d)]
  have hh : (axisDomain d).indicator (fun p:ℝ×ℝ=>w p*F (p.1*p.2))=
      fun p=>markedWeight d w p*F (p.1*p.2) := by
    ext p
    by_cases hp:p∈axisDomain d <;> simp [markedWeight,hp]
  have hm := markedWeight_measurable d hw
  rw [hh,lintegral_prod _ (by fun_prop : Measurable (fun p:ℝ×ℝ=>markedWeight d w p*F (p.1*p.2))).aemeasurable]
  exact actual_product_pushforward (markedWeight_measurable d hw) F hF

end
end Resonance.MarkedProductDensity
