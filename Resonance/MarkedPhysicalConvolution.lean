import Resonance.MarkedAxisCoordinates
import Resonance.MarkedEnergyDensity
import Resonance.CollisionFrequencyConvolution

/-! Original marked fixed-output mass at energy zero, identified with
the marked complete three-axis convolution through the actual pushforward. -/
open Real Set MeasureTheory
open scoped ENNReal Topology
namespace Resonance.MarkedPhysicalConvolution
noncomputable section
open PlaneCoarea CubeAxisCoordinates MarkedProductDensity MarkedDensityContinuity
open MarkedAxisCoordinates MarkedEnergyDensity CollisionFrequencyConvolution
set_option maxHeartbeats 1200000

def axisMark (w : ℝ×ℝ→ℝ) (q : FourMomenta) : ℝ :=
  w ((q 2-q 0) 0,(q 3-q 0) 0)

theorem axisMark_continuous {w : ℝ×ℝ→ℝ} (hw : Continuous w) :
    Continuous (axisMark w) := by unfold axisMark; fun_prop

theorem axisMark_rectangle (w : ℝ×ℝ→ℝ) (k x y : E) :
    axisMark w (rectangleFour k x y)=w (x 0,y 0) := by
  simp [axisMark,rectangleFour]

def normalizedDensity (d : Fin 3→ℝ) (w : ℝ×ℝ→ℝ) (e : ℝ) : ℝ≥0∞ :=
  (1/2:ℝ≥0∞)*markedSum (productDensity (markedWeight (d 0)
    (fun p=>ENNReal.ofReal (w p)))) (d 1) (d 2) (e/2)

theorem normalizedDensity_continuous {d : Fin 3→ℝ}
    (hd0 : ∀i,0≤d i) (hd1 : ∀i,d i<1) {w : ℝ×ℝ→ℝ}
    (hw : Continuous w) (hb : ∀p,w p≤1) : Continuous (normalizedDensity d w) := by
  have hc := actual_marked_sum_continuous (hd0 0) (hd1 0)
    (hd0 1) (hd1 1).le (hd0 2) (hd1 2).le hw.measurable.ennreal_ofReal
    (fun p=>ENNReal.ofReal_le_one.mpr (hb p))
  exact (ENNReal.continuous_const_mul (by norm_num : (1/2:ℝ≥0∞)≠∞)).comp
    (hc.comp (by fun_prop))

theorem actual_normalized_density_lintegral {d : Fin 3→ℝ}
    (hd0 : ∀i,0≤d i) (hd1 : ∀i,d i<1) {w : ℝ×ℝ→ℝ}
    (hw : Continuous w) (hb : ∀p,w p≤1) (F : ℝ→ℝ≥0∞) (hF : Measurable F) :
    (∫⁻e:ℝ,F e*density (1/2) (axisMark w) (normalizedOutput d) e)=
      ∫⁻e:ℝ,F e*normalizedDensity d w e := by
  classical
  rw [←actual_weighted_energy_density (1/2) (axisMark w)
    (axisMark_continuous hw).measurable (normalizedOutput d) F hF]
  have he : (∫⁻p:E×E,(CoareaNormalization.allFourFlags (1/2)).indicator
      (fun q=>ENNReal.ofReal (axisMark w q)*F (CoareaNormalization.energy q))
        (rectangleFour (normalizedOutput d) p.1 p.2)∂((volume:Measure E).prod volume))=
      ∫⁻e:ℝ,F (2*e)*markedSum (productDensity (markedWeight (d 0)
        (fun p=>ENNReal.ofReal (w p)))) (d 1) (d 2) e := by
    rw [←actual_normalized_marked_source hd0 hd1 hw.measurable.ennreal_ofReal
      (fun t=>F (2*t)) (by fun_prop)]
    apply lintegral_congr
    intro p
    by_cases hp:∀l:Fin 4,rectangleFour (normalizedOutput d) p.1 p.2 l∈ResonantMeasure.cube (1/2)
    · simp only [Set.indicator_apply,mem_setOf_eq,CoareaNormalization.allFourFlags,hp,
        axisMark_rectangle,rectangleFour_energy]
    · simp only [Set.indicator_apply,mem_setOf_eq,CoareaNormalization.allFourFlags,hp,if_false]
  rw [he]
  have hc := actual_marked_sum_continuous (hd0 0) (hd1 0)
    (hd0 1) (hd1 1).le (hd0 2) (hd1 2).le hw.measurable.ennreal_ofReal
    (fun p=>ENNReal.ofReal_le_one.mpr (hb p))
  rw [positive_scale_lintegral (by norm_num : (0:ℝ)<2) F _ hF hc.measurable]
  have hm : Measurable (fun e:ℝ=>F e*markedSum (productDensity (markedWeight (d 0)
      (fun p=>ENNReal.ofReal (w p)))) (d 1) (d 2) (e/2)) := hF.mul (hc.measurable.comp (by fun_prop))
  rw [←lintegral_const_mul _ hm]
  apply lintegral_congr
  intro e
  unfold normalizedDensity
  norm_num only [ENNReal.ofReal_inv_of_pos (by norm_num : (0:ℝ)<2),
    ENNReal.ofReal_div_of_pos (by norm_num : (0:ℝ)<2),ENNReal.ofReal_one,ENNReal.ofReal_ofNat]
  ring

theorem actual_normalized_density_ae_eq {d : Fin 3→ℝ}
    (hd0 : ∀i,0≤d i) (hd1 : ∀i,d i<1) {w : ℝ×ℝ→ℝ}
    (hw : Continuous w) (hb : ∀p,w p≤1) :
    density (1/2) (axisMark w) (normalizedOutput d)=ᵐ[(volume:Measure ℝ)] normalizedDensity d w := by
  have hm := density_measurable (1/2) (axisMark_continuous hw).measurable (normalizedOutput d)
  have hn := (normalizedDensity_continuous hd0 hd1 hw hb).measurable
  apply (withDensity_eq_iff_of_sigmaFinite hm.aemeasurable hn.aemeasurable).mp
  apply Measure.ext_of_lintegral
  intro F hF
  rw [lintegral_withDensity_eq_lintegral_mul _ hm hF,
    lintegral_withDensity_eq_lintegral_mul _ hn hF]
  simpa only [mul_comm] using actual_normalized_density_lintegral hd0 hd1 hw hb F hF

theorem original_normalized_marked_frequency {d : Fin 3→ℝ}
    (hd0 : ∀i,0≤d i) (hd1 : ∀i,d i<1) {w : ℝ×ℝ→ℝ}
    (hw : Continuous w) (hp : ∀p,0≤w p) (hb : ∀p,w p≤1) :
    ENNReal.ofReal (FiberContinuity.fiberReadout (1/2) (axisMark w) (normalizedOutput d))=
      (1/2:ℝ≥0∞)*markedSum (productDensity (markedWeight (d 0)
        (fun p=>ENNReal.ofReal (w p)))) (d 1) (d 2) 0 := by
  have h := continuousAt_zero_eq_of_ae_eq (actual_normalized_density_ae_eq hd0 hd1 hw hb)
    (density_continuousAt_zero (by norm_num) (axisMark w) (axisMark_continuous hw)
      (fun q=>hp _) (normalizedOutput d) (normalizedOutput_mem hd0 (fun i=>(hd1 i).le)))
    (normalizedDensity_continuous hd0 hd1 hw hb).continuousAt
  rw [density_zero_original (by norm_num : (0:ℝ)≤1/2) (axisMark w)
    (axisMark_continuous hw) (fun q=>hp _) (normalizedOutput d)] at h
  simpa only [normalizedDensity,zero_div] using h

end
end Resonance.MarkedPhysicalConvolution
