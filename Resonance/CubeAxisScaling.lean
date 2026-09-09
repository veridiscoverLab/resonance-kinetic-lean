import Resonance.CubeAxisCoordinates
import Resonance.FixedEnergyDensity
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-! The original dimensional factors for dilation of all six physical
coordinates.  No cutoff or auxiliary collision frequency is introduced. -/
open Real Set MeasureTheory
open scoped ENNReal Topology
namespace Resonance.CubeAxisScaling
noncomputable section
set_option maxHeartbeats 800000
open Resonance.PlaneCoarea
open Resonance.ResonantMeasure (cube)
open Resonance.CubeAxisCoordinates Resonance.CornerConvolution
open Resonance.FixedEnergyDensity

def scalePair (L:ℝ) (p:E×E) : E×E := L•p

theorem scalePair_preserving {L:ℝ} (hL:0<L) :
    MeasurePreserving (scalePair L)
      (ENNReal.ofReal (L^6)•(volume:Measure (E×E))) volume := by
  letI : (volume:Measure (E×E)).IsAddHaarMeasure :=
    Measure.prod.instIsAddHaarMeasure (volume:Measure E) (volume:Measure E)
  refine ⟨by unfold scalePair; fun_prop,?_⟩
  have hdim : Module.finrank ℝ (E×E)=6 := by simp
  change Measure.map (fun p:E×E=>L•p) (ENNReal.ofReal (L^6)•volume)=volume
  rw [Measure.map_smul,Measure.map_addHaar_smul (volume:Measure (E×E)) hL.ne',hdim,
    abs_of_pos (inv_pos.mpr (pow_pos hL 6)),smul_smul,
    ←ENNReal.ofReal_mul (pow_nonneg hL.le 6),mul_inv_cancel₀ (pow_ne_zero 6 hL.ne'),
    ENNReal.ofReal_one,one_smul]

theorem cube_smul_iff {L:ℝ} (hL:0<L) (k:E) :
    L•k∈cube (L/2) ↔ k∈cube (1/2) := by
  change (∀i:Fin 3,|L*k i|≤L/2) ↔ (∀i:Fin 3,|k i|≤(1/2:ℝ))
  apply forall_congr'
  intro i
  rw [abs_mul,abs_of_pos hL]
  constructor <;> intro h <;> nlinarith

theorem rectangleFour_smul (L:ℝ) (k x y:E) :
    rectangleFour (L•k) (L•x) (L•y)=L•rectangleFour k x y := by
  ext l j
  fin_cases l <;> simp [rectangleFour,smul_add]

theorem scaled_flags_iff {L:ℝ} (hL:0<L) (k:E) (p:E×E) :
    scalePair L p∈sharpPairSet (L/2) (L•k) ↔ p∈sharpPairSet (1/2) k := by
  change (∀l:Fin 4,rectangleFour (L•k) (L•p.1) (L•p.2) l∈cube (L/2)) ↔
    (∀l:Fin 4,rectangleFour k p.1 p.2 l∈cube (1/2))
  rw [rectangleFour_smul]
  exact forall_congr' (fun l=>cube_smul_iff hL _)

theorem scalePair_inner (L:ℝ) (p:E×E) :
    inner ℝ (scalePair L p).1 (scalePair L p).2=L^2*inner ℝ p.1 p.2 := by
  change inner ℝ (L•p.1) (L•p.2)=_
  rw [real_inner_smul_left,real_inner_smul_right]
  ring

def scalarSharpReadout (R:ℝ) (k:E) (F:ℝ→ℝ≥0∞) : E×E→ℝ≥0∞ :=
  (sharpPairSet R k).indicator (fun p=>F (inner ℝ p.1 p.2))

theorem scalarSharpReadout_measurable (R:ℝ) (k:E) (F:ℝ→ℝ≥0∞) (hF:Measurable F) :
    Measurable (scalarSharpReadout R k F) :=
  (hF.comp (by fun_prop)).indicator (sharpPairSet_measurable R k)

theorem full_scaled_scalar_lintegral {L:ℝ} (hL:0<L) {d:Fin 3→ℝ}
    (hd0:∀i,0≤d i) (hd1:∀i,d i<1) (F:ℝ→ℝ≥0∞) (hF:Measurable F) :
    (∫⁻p:E×E,scalarSharpReadout (L/2) (L•normalizedOutput d) F p)=
      ENNReal.ofReal (L^6)*(∫⁻t:ℝ,F (L^2*t)*sumDensity d t) := by
  classical
  have hm := scalarSharpReadout_measurable (L/2) (L•normalizedOutput d) F hF
  have he := lintegral_map (μ:=ENNReal.ofReal (L^6)•(volume:Measure (E×E)))
    hm (scalePair_preserving hL).measurable
  rw [(scalePair_preserving hL).map_eq,lintegral_smul_measure,smul_eq_mul] at he
  rw [he]
  congr 1
  rw [←normalized_sharp_lintegral hd0 hd1 (fun t=>F (L^2*t)) (by fun_prop)]
  apply lintegral_congr
  intro p
  unfold scalarSharpReadout
  simp only [Set.indicator_apply,mem_setOf_eq]
  simp only [scaled_flags_iff hL,scalePair_inner]
  simp only [sharpPairSet,CoareaNormalization.allFourFlags,mem_setOf_eq]
  simp

end
end Resonance.CubeAxisScaling
