import Resonance.MarkedPhysicalConvolution

/-! Simultaneous dilation of the original six physical integration
coordinates, retaining the same marked axis and exact dimensional factors. -/
open Real Set MeasureTheory
open scoped ENNReal Topology
namespace Resonance.MarkedPhysicalScaling
noncomputable section
open PlaneCoarea CubeAxisCoordinates CubeAxisScaling FixedEnergyDensity
open MarkedProductDensity MarkedDensityContinuity MarkedAxisCoordinates
open MarkedEnergyDensity CollisionFrequencyConvolution MarkedPhysicalConvolution
set_option maxHeartbeats 1400000

def scaledMark (L : ℝ) (w : ℝ×ℝ→ℝ) (q : FourMomenta) : ℝ :=
  axisMark w (L⁻¹•q)

theorem scaledMark_continuous (L : ℝ) {w : ℝ×ℝ→ℝ} (hw : Continuous w) :
    Continuous (scaledMark L w) := by unfold scaledMark; exact (axisMark_continuous hw).comp (by fun_prop)

theorem scaledMark_dilated {L : ℝ} (hL : 0<L) (w : ℝ×ℝ→ℝ) (k x y : E) :
    scaledMark L w (rectangleFour (L•k) (L•x) (L•y))=w (x 0,y 0) := by
  rw [scaledMark,rectangleFour_smul,inv_smul_smul₀ hL.ne',axisMark_rectangle]

def scalarReadout (L : ℝ) (d : Fin 3→ℝ) (w : ℝ×ℝ→ℝ) (F : ℝ→ℝ≥0∞) : E×E→ℝ≥0∞ :=
  (sharpPairSet (L/2) (L•normalizedOutput d)).indicator
    (fun p=>ENNReal.ofReal (scaledMark L w (rectangleFour (L•normalizedOutput d) p.1 p.2))*
      F (inner ℝ p.1 p.2))

theorem scalarReadout_measurable (L : ℝ) (d : Fin 3→ℝ) {w : ℝ×ℝ→ℝ}
    (hw : Continuous w) {F : ℝ→ℝ≥0∞} (hF : Measurable F) :
    Measurable (scalarReadout L d w F) := by
  have hm : Measurable (fun p:E×E=>ENNReal.ofReal
      (scaledMark L w (rectangleFour (L•normalizedOutput d) p.1 p.2))*F (inner ℝ p.1 p.2)) := by
    have h := (scaledMark_continuous L hw).measurable
    have hc := rectangleFour_continuous.measurable
    fun_prop
  exact hm.indicator (sharpPairSet_measurable _ _)

theorem full_scaled_marked_lintegral {L : ℝ} (hL : 0<L) {d : Fin 3→ℝ}
    (hd0 : ∀i,0≤d i) (hd1 : ∀i,d i<1) {w : ℝ×ℝ→ℝ}
    (hw : Continuous w) (F : ℝ→ℝ≥0∞) (hF : Measurable F) :
    (∫⁻p:E×E,scalarReadout L d w F p)=ENNReal.ofReal (L^6)*
      ∫⁻t:ℝ,F (L^2*t)*markedSum (productDensity (markedWeight (d 0)
        (fun p=>ENNReal.ofReal (w p)))) (d 1) (d 2) t := by
  classical
  have he := lintegral_map (μ:=ENNReal.ofReal (L^6)•(volume:Measure (E×E)))
    (scalarReadout_measurable L d hw hF) (scalePair_preserving hL).measurable
  rw [(scalePair_preserving hL).map_eq,lintegral_smul_measure,smul_eq_mul] at he
  rw [he]
  congr 1
  rw [←actual_normalized_marked_source hd0 hd1 hw.measurable.ennreal_ofReal
    (fun t=>F (L^2*t)) (by fun_prop)]
  apply lintegral_congr
  intro p
  unfold scalarReadout
  simp only [Set.indicator_apply,mem_setOf_eq]
  simp only [scaled_flags_iff hL,scalePair_inner]
  change (if p∈sharpPairSet (1/2) (normalizedOutput d) then
    ENNReal.ofReal (scaledMark L w (rectangleFour (L•normalizedOutput d) (L•p.1) (L•p.2)))*
      F (L^2*inner ℝ p.1 p.2) else 0)=_
  rw [scaledMark_dilated hL]
  simp only [sharpPairSet,CoareaNormalization.allFourFlags,mem_setOf_eq]

def scaledDensity (L : ℝ) (d : Fin 3→ℝ) (w : ℝ×ℝ→ℝ) (e : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (L^4/2)*markedSum (productDensity (markedWeight (d 0)
    (fun p=>ENNReal.ofReal (w p)))) (d 1) (d 2) (e/(2*L^2))

theorem scaledDensity_continuous {d : Fin 3→ℝ}
    (hd0 : ∀i,0≤d i) (hd1 : ∀i,d i<1) (L : ℝ) {w : ℝ×ℝ→ℝ}
    (hw : Continuous w) (hb : ∀p,w p≤1) : Continuous (scaledDensity L d w) := by
  have hc := actual_marked_sum_continuous (hd0 0) (hd1 0)
    (hd0 1) (hd1 1).le (hd0 2) (hd1 2).le hw.measurable.ennreal_ofReal
    (fun p=>ENNReal.ofReal_le_one.mpr (hb p))
  exact (ENNReal.continuous_const_mul ENNReal.ofReal_ne_top).comp (hc.comp (by fun_prop))

theorem actual_scaled_density_lintegral {L : ℝ} (hL : 0<L) {d : Fin 3→ℝ}
    (hd0 : ∀i,0≤d i) (hd1 : ∀i,d i<1) {w : ℝ×ℝ→ℝ}
    (hw : Continuous w) (hb : ∀p,w p≤1) (F : ℝ→ℝ≥0∞) (hF : Measurable F) :
    (∫⁻e:ℝ,F e*density (L/2) (scaledMark L w) (L•normalizedOutput d) e)=
      ∫⁻e:ℝ,F e*scaledDensity L d w e := by
  classical
  rw [←actual_weighted_energy_density (L/2) (scaledMark L w)
    (scaledMark_continuous L hw).measurable (L•normalizedOutput d) F hF]
  have he : (∫⁻p:E×E,(CoareaNormalization.allFourFlags (L/2)).indicator
      (fun q=>ENNReal.ofReal (scaledMark L w q)*F (CoareaNormalization.energy q))
        (rectangleFour (L•normalizedOutput d) p.1 p.2)∂((volume:Measure E).prod volume))=
      ∫⁻p:E×E,scalarReadout L d w (fun t=>F (2*t)) p := by
    apply lintegral_congr
    intro p
    simp only [scalarReadout,Set.indicator_apply,sharpPairSet,mem_setOf_eq,rectangleFour_energy]
  rw [he,full_scaled_marked_lintegral hL hd0 hd1 hw (fun t=>F (2*t)) (by fun_prop)]
  have hc := actual_marked_sum_continuous (hd0 0) (hd1 0)
    (hd0 1) (hd1 1).le (hd0 2) (hd1 2).le hw.measurable.ennreal_ofReal
    (fun p=>ENNReal.ofReal_le_one.mpr (hb p))
  have hassoc (t:ℝ) : 2*(L^2*t)=(2*L^2)*t := by ring
  simp_rw [hassoc]
  rw [positive_scale_lintegral (by positivity : 0<2*L^2) F _ hF hc.measurable,
    ←mul_assoc,←ENNReal.ofReal_mul (pow_nonneg hL.le 6)]
  have hcoeff : L^6*(2*L^2)⁻¹=L^4/2 := by field_simp
  rw [hcoeff]
  have hm : Measurable (fun e:ℝ=>F e*markedSum (productDensity (markedWeight (d 0)
      (fun p=>ENNReal.ofReal (w p)))) (d 1) (d 2) (e/(2*L^2))) :=
    hF.mul (hc.measurable.comp (by fun_prop))
  rw [←lintegral_const_mul _ hm]
  apply lintegral_congr
  intro e
  unfold scaledDensity
  ring

theorem original_scaled_marked_frequency {L : ℝ} (hL : 0<L) {d : Fin 3→ℝ}
    (hd0 : ∀i,0≤d i) (hd1 : ∀i,d i<1) {w : ℝ×ℝ→ℝ}
    (hw : Continuous w) (hp : ∀p,0≤w p) (hb : ∀p,w p≤1) :
    ENNReal.ofReal (FiberContinuity.fiberReadout (L/2) (scaledMark L w) (L•normalizedOutput d))=
      ENNReal.ofReal (L^4/2)*markedSum (productDensity (markedWeight (d 0)
        (fun p=>ENNReal.ofReal (w p)))) (d 1) (d 2) 0 := by
  have hm := density_measurable (L/2) (scaledMark_continuous L hw).measurable (L•normalizedOutput d)
  have hn := (scaledDensity_continuous hd0 hd1 L hw hb).measurable
  have hae : density (L/2) (scaledMark L w) (L•normalizedOutput d)=ᵐ[(volume:Measure ℝ)]
      scaledDensity L d w := by
    apply (withDensity_eq_iff_of_sigmaFinite hm.aemeasurable hn.aemeasurable).mp
    apply Measure.ext_of_lintegral
    intro F hF
    rw [lintegral_withDensity_eq_lintegral_mul _ hm hF,lintegral_withDensity_eq_lintegral_mul _ hn hF]
    simpa only [mul_comm] using actual_scaled_density_lintegral hL hd0 hd1 hw hb F hF
  have h := continuousAt_zero_eq_of_ae_eq hae
    (density_continuousAt_zero (by positivity) (scaledMark L w) (scaledMark_continuous L hw)
      (fun q=>hp _) _ ((cube_smul_iff hL _).mpr (normalizedOutput_mem hd0 (fun i=>(hd1 i).le))))
    (scaledDensity_continuous hd0 hd1 L hw hb).continuousAt
  rw [density_zero_original (by positivity : 0≤L/2) (scaledMark L w)
    (scaledMark_continuous L hw) (fun q=>hp _)] at h
  simpa only [scaledDensity,zero_div] using h

end
end Resonance.MarkedPhysicalScaling
