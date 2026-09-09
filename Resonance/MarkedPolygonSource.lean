import Resonance.MarkedDensityContinuity

/-! A mark on an original coordinate pair propagates through the entire
three-polygon source before imposing the common energy constraint. -/
open Real Set MeasureTheory
open scoped ENNReal
namespace Resonance.MarkedPolygonSource
noncomputable section
open CornerProductCoordinates AxisProductDensity CornerConvolution
open MarkedProductDensity MarkedDensityContinuity
set_option maxHeartbeats 1000000

def source (d : Fin 3→ℝ) (w : ℝ×ℝ→ℝ≥0∞) (F : ℝ→ℝ≥0∞) : ℝ≥0∞ :=
  ∫⁻p0 in axisDomain (d 0),w p0*
    (∫⁻p1 in axisDomain (d 1),∫⁻p2 in axisDomain (d 2),
      F (p0.1*p0.2+p1.1*p1.2+p2.1*p2.2)
      ∂((volume:Measure ℝ).prod volume)
    ∂((volume:Measure ℝ).prod volume))∂((volume:Measure ℝ).prod volume)

theorem source_density (d : Fin 3→ℝ) (hd0 : ∀i,0≤d i) (hd1 : ∀i,d i<1)
    {w : ℝ×ℝ→ℝ≥0∞} (hw : Measurable w) (F : ℝ→ℝ≥0∞) (hF : Measurable F) :
    source d w F=∫⁻E:ℝ,F E*markedSum (productDensity (markedWeight (d 0) w)) (d 1) (d 2) E := by
  unfold source
  have h2 (s t:ℝ) := full_axis_product_lintegral (hd0 2) (hd1 2)
    (fun u=>F (s+t+u)) (by fun_prop)
  simp_rw [h2]
  have h1 (s:ℝ) : Measurable (fun t:ℝ=>∫⁻u:ℝ,F (s+t+u)*axisDensity (d 2) u) := by
    have hh : Measurable (fun p:ℝ×ℝ=>F (s+p.1+p.2)*axisDensity (d 2) p.2) :=
      (hF.comp (by fun_prop)).mul ((axisDensity_measurable _).comp measurable_snd)
    exact hh.lintegral_prod_right'
  have he1 (s:ℝ) := full_axis_product_lintegral (hd0 1) (hd1 1)
    (fun t=>∫⁻u:ℝ,F (s+t+u)*axisDensity (d 2) u) (h1 s)
  simp_rw [he1]
  have h0 : Measurable (fun s:ℝ=>∫⁻t:ℝ,
      (∫⁻u:ℝ,F (s+t+u)*axisDensity (d 2) u)*axisDensity (d 1) t) := by
    have hh : Measurable (fun p:(ℝ×ℝ)×ℝ=>
        F (p.1.1+p.1.2+p.2)*axisDensity (d 2) p.2) :=
      (hF.comp (by fun_prop)).mul ((axisDensity_measurable _).comp measurable_snd)
    exact (hh.lintegral_prod_right'.mul
      ((axisDensity_measurable _).comp measurable_snd)).lintegral_prod_right'
  rw [actual_marked_polygon_density (d 0) hw _ h0]
  unfold markedSum
  rw [←triple_density_sum (productDensity (markedWeight (d 0) w))
    (axisDensity (d 1)) (axisDensity (d 2)) F
    (productDensity_measurable (markedWeight_measurable _ hw))
    (axisDensity_measurable _) (axisDensity_measurable _) hF]
  apply lintegral_congr
  intro s
  have hm : Measurable (fun t:ℝ=>
      (∫⁻u:ℝ,F (s+t+u)*axisDensity (d 2) u)*axisDensity (d 1) t) :=
    (h1 s).mul (axisDensity_measurable _)
  rw [←lintegral_mul_const _ hm]
  apply lintegral_congr
  intro t
  have hh : Measurable (fun u:ℝ=>F (s+t+u)*axisDensity (d 2) u) :=
    (hF.comp (by fun_prop)).mul (axisDensity_measurable _)
  rw [←lintegral_mul_const _ hh,←lintegral_mul_const _ (hh.mul measurable_const)]
  apply lintegral_congr
  intro u
  ring

end
end Resonance.MarkedPolygonSource
