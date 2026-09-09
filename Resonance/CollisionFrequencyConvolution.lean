import Resonance.CubeAxisScaling
import Resonance.CornerConvolutionContinuity
import Mathlib.MeasureTheory.Function.AEEqOfLIntegral

/-! Pointwise identification of the original fixed-output collision
frequency with the complete three-axis density at energy zero. -/
open Real Set MeasureTheory Filter
open scoped ENNReal Topology
namespace Resonance.CollisionFrequencyConvolution
noncomputable section
set_option maxHeartbeats 1000000
open Resonance.PlaneCoarea Resonance.CubeAxisCoordinates Resonance.CubeAxisScaling
open Resonance.FixedEnergyDensity Resonance.CornerConvolution
open Resonance.CornerConvolutionContinuity

theorem positive_scale_lintegral {a:ℝ} (ha:0<a) (F H:ℝ→ℝ≥0∞)
    (hF:Measurable F) (hH:Measurable H) :
    (∫⁻t:ℝ,F (a*t)*H t)=ENNReal.ofReal a⁻¹*(∫⁻e:ℝ,F e*H (e/a)) := by
  have hm : Measurable (fun e:ℝ=>F e*H (e/a)) := hF.mul (hH.comp (by fun_prop))
  have he := lintegral_map (μ:=(volume:Measure ℝ)) hm
    (by fun_prop : Measurable (fun t:ℝ=>a*t))
  rw [Real.map_volume_mul_left ha.ne',lintegral_smul_measure,smul_eq_mul,
    abs_of_pos (inv_pos.mpr ha)] at he
  have hcancel (t:ℝ) : a*t/a=t := by field_simp
  simpa only [hcancel] using he.symm

theorem sharp_energy_eq_scalar {R:ℝ} (hR:0≤R) (k:E)
    (F:ℝ→ℝ≥0∞) (hF:Measurable F) :
    (∫⁻e:ℝ,F e*fiberDensity R k e)=
      ∫⁻p:E×E,scalarSharpReadout R k (fun t=>F (2*t)) p := by
  classical
  rw [←sharp_energy_density hR k F hF]
  apply lintegral_congr
  intro p
  by_cases hp:rectangleFour k p.1 p.2∈CoareaNormalization.allFourFlags R
  · have hsp:p∈sharpPairSet R k := hp
    simp only [scalarSharpReadout,Set.indicator_of_mem hp,Set.indicator_of_mem hsp,
      rectangleFour_energy]
  · have hsp:p∉sharpPairSet R k := hp
    simp only [scalarSharpReadout,Set.indicator_of_notMem hp,Set.indicator_of_notMem hsp]

def scaledDensity (L:ℝ) (d:Fin 3→ℝ) (e:ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (L^4/2)*sumDensity d (e/(2*L^2))

theorem scaledDensity_continuous {d:Fin 3→ℝ}
    (hd0:∀i,0≤d i) (hd1:∀i,d i≤1) (L:ℝ) : Continuous (scaledDensity L d) :=
  (ENNReal.continuous_const_mul ENNReal.ofReal_ne_top).comp
    ((sumDensity_continuous hd0 hd1).comp (by fun_prop))

theorem physical_density_lintegral {L:ℝ} (hL:0<L) {d:Fin 3→ℝ}
    (hd0:∀i,0≤d i) (hd1:∀i,d i<1) (F:ℝ→ℝ≥0∞) (hF:Measurable F) :
    (∫⁻e:ℝ,F e*fiberDensity (L/2) (L•normalizedOutput d) e)=
      ∫⁻e:ℝ,F e*scaledDensity L d e := by
  rw [sharp_energy_eq_scalar (by positivity) _ F hF,
    full_scaled_scalar_lintegral hL hd0 hd1 (fun t=>F (2*t)) (by fun_prop)]
  have ha:0<2*L^2 := by positivity
  have hassoc (t:ℝ) : 2*(L^2*t)=(2*L^2)*t := by ring
  simp_rw [hassoc]
  rw [positive_scale_lintegral ha F (sumDensity d) hF (sumDensity_measurable d)]
  rw [←mul_assoc,←ENNReal.ofReal_mul (pow_nonneg hL.le 6)]
  have hcoeff : L^6*(2*L^2)⁻¹=L^4/2 := by field_simp
  rw [hcoeff]
  have hm : Measurable (fun e:ℝ=>F e*sumDensity d (e/(2*L^2))) :=
    hF.mul ((sumDensity_measurable d).comp (by fun_prop))
  rw [←lintegral_const_mul _ hm]
  apply lintegral_congr
  intro e
  unfold scaledDensity
  ring

theorem physical_density_ae_eq {L:ℝ} (hL:0<L) {d:Fin 3→ℝ}
    (hd0:∀i,0≤d i) (hd1:∀i,d i<1) :
    fiberDensity (L/2) (L•normalizedOutput d)=ᵐ[(volume:Measure ℝ)] scaledDensity L d := by
  apply (withDensity_eq_iff_of_sigmaFinite
    (fiberDensity_measurable (by positivity) _).aemeasurable
    (scaledDensity_continuous hd0 (fun i=>(hd1 i).le) L).measurable.aemeasurable).mp
  apply Measure.ext_of_lintegral
  intro F hF
  rw [lintegral_withDensity_eq_lintegral_mul _ (fiberDensity_measurable (by positivity) _) hF,
    lintegral_withDensity_eq_lintegral_mul _
      (scaledDensity_continuous hd0 (fun i=>(hd1 i).le) L).measurable hF]
  simpa only [mul_comm] using physical_density_lintegral hL hd0 hd1 F hF

theorem continuousAt_zero_eq_of_ae_eq {f g:ℝ→ℝ≥0∞}
    (hfg:f=ᵐ[(volume:Measure ℝ)]g) (hf:ContinuousAt f 0) (hg:ContinuousAt g 0) : f 0=g 0 := by
  have hd : Dense {x:ℝ | f x=g x} := Measure.dense_of_ae hfg
  have hc : (0:ℝ)∈closure {x:ℝ | f x=g x} := hd 0
  haveI : NeBot (𝓝[{x:ℝ | f x=g x}] (0:ℝ)) := mem_closure_iff_nhdsWithin_neBot.mp hc
  have he : f=ᶠ[𝓝[{x:ℝ | f x=g x}] (0:ℝ)]g := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    exact hx
  exact tendsto_nhds_unique (hf.mono_left nhdsWithin_le_nhds)
    ((hg.mono_left nhdsWithin_le_nhds).congr' he.symm)

/-- Actual original frequency, exact dimensional factor and every
approach with 0≤d_i<1.  Zero-energy equality is obtained only after
both actual representatives have been proved continuous there. -/
theorem original_frequency_eq_convolution {L:ℝ} (hL:0<L) {d:Fin 3→ℝ}
    (hd0:∀i,0≤d i) (hd1:∀i,d i<1) :
    ENNReal.ofReal (CollisionFrequency.geometricFrequency (L/2) (L•normalizedOutput d))=
      ENNReal.ofReal (L^4/2)*sumDensity d 0 := by
  have hk : L•normalizedOutput d∈ResonantMeasure.cube (L/2) :=
    (cube_smul_iff hL _).mpr (normalizedOutput_mem hd0 (fun i=>(hd1 i).le))
  have h := continuousAt_zero_eq_of_ae_eq (physical_density_ae_eq hL hd0 hd1)
    (fiberDensity_continuousAt_zero (by positivity) _ hk)
    (scaledDensity_continuous hd0 (fun i=>(hd1 i).le) L).continuousAt
  simpa only [fiberDensity_zero,scaledDensity,zero_div] using h

end
end Resonance.CollisionFrequencyConvolution
