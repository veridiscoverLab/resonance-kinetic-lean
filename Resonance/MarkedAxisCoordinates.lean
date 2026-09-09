import Resonance.MarkedPolygonSource

/-! The marked complete polygon source equals the original physical
six-dimensional sharp integral, with the very same marked coordinate pair. -/
open Real Set MeasureTheory
open scoped ENNReal
namespace Resonance.MarkedAxisCoordinates
noncomputable section
open CornerProductCoordinates AxisProductDensity CubeAxisCoordinates PlaneCoarea
open MarkedProductDensity MarkedDensityContinuity MarkedPolygonSource
open ResonantMeasure (cube)
set_option maxHeartbeats 1000000

theorem source_full_integral (d : Fin 3→ℝ) {w : ℝ×ℝ→ℝ≥0∞}
    (hw : Measurable w) (F : ℝ→ℝ≥0∞) (hF : Measurable F) :
    source d w F=∫⁻p:TriplePair,
      (axisDomain (d 0)×ˢ(axisDomain (d 1)×ˢaxisDomain (d 2))).indicator
        (fun p=>w p.1*F (p.1.1*p.1.2+p.2.1.1*p.2.1.2+p.2.2.1*p.2.2.2)) p := by
  have hs : MeasurableSet (axisDomain (d 0)×ˢ(axisDomain (d 1)×ˢaxisDomain (d 2))) :=
    (axisDomain_measurable _).prod ((axisDomain_measurable _).prod (axisDomain_measurable _))
  rw [lintegral_indicator hs]
  change source d w F=∫⁻p:TriplePair,
    w p.1*F (p.1.1*p.1.2+p.2.1.1*p.2.1.2+p.2.2.1*p.2.2.2)
    ∂(((volume:Measure AxisPair).prod ((volume:Measure AxisPair).prod volume)).restrict
      (axisDomain (d 0)×ˢ(axisDomain (d 1)×ˢaxisDomain (d 2))))
  rw [←Measure.prod_restrict,←Measure.prod_restrict]
  have hh : Measurable (fun p:TriplePair=>w p.1*
      F (p.1.1*p.1.2+p.2.1.1*p.2.1.2+p.2.2.1*p.2.2.2)) := by fun_prop
  rw [lintegral_prod _ hh.aemeasurable]
  apply lintegral_congr
  intro p0
  have hi : Measurable (fun p:AxisPair×AxisPair=>
      F (p0.1*p0.2+p.1.1*p.1.2+p.2.1*p.2.2)) := by fun_prop
  dsimp only
  rw [lintegral_const_mul _ hi]
  congr 1
  rw [lintegral_prod _ hi.aemeasurable]
  rfl

theorem actual_normalized_marked_source {d : Fin 3→ℝ}
    (hd0 : ∀i,0≤d i) (hd1 : ∀i,d i<1) {w : ℝ×ℝ→ℝ≥0∞}
    (hw : Measurable w) (F : ℝ→ℝ≥0∞) (hF : Measurable F) :
    (∫⁻p:PlaneCoarea.E×PlaneCoarea.E,
      {p:PlaneCoarea.E×PlaneCoarea.E | ∀l:Fin 4,
        rectangleFour (normalizedOutput d) p.1 p.2 l∈cube (1/2)}.indicator
        (fun p=>w (p.1 0,p.2 0)*F (inner ℝ p.1 p.2)) p)=
      ∫⁻E:ℝ,F E*markedSum (productDensity (markedWeight (d 0) w)) (d 1) (d 2) E := by
  classical
  rw [←source_density d hd0 hd1 hw F hF,source_full_integral d hw F hF]
  let G : PlaneCoarea.E×PlaneCoarea.E→ℝ≥0∞ :=
    {p | ∀l:Fin 4,rectangleFour (normalizedOutput d) p.1 p.2 l∈cube (1/2)}.indicator
      (fun p=>w (p.1 0,p.2 0)*F (inner ℝ p.1 p.2))
  have hflags : MeasurableSet {p:PlaneCoarea.E×PlaneCoarea.E | ∀l:Fin 4,
      rectangleFour (normalizedOutput d) p.1 p.2 l∈cube (1/2)} :=
    (CoareaNormalization.allFourFlags_measurable (1/2)).preimage
      (rectangleFour_continuous.measurable.comp
        (measurable_const.prodMk (measurable_fst.prodMk measurable_snd)))
  have hG : Measurable G := (show Measurable (fun p:PlaneCoarea.E×PlaneCoarea.E=>
    w (p.1 0,p.2 0)*F (inner ℝ p.1 p.2)) by fun_prop).indicator hflags
  have he := lintegral_map (μ:=(volume:Measure TriplePair)) hG tripleToPair_preserving.measurable
  rw [tripleToPair_preserving.map_eq] at he
  change (∫⁻p:PlaneCoarea.E×PlaneCoarea.E,G p)=_
  rw [he]
  apply lintegral_congr
  intro p
  dsimp only [G]
  simp only [Set.indicator_apply,mem_setOf_eq,mem_prod]
  simp only [normalized_full_flags hd0 (fun i=>(hd1 i).le),tripleToPair_inner,
    tripleToPair_fst,tripleToPair_snd,tripleToPi_zero]

end
end Resonance.MarkedAxisCoordinates
