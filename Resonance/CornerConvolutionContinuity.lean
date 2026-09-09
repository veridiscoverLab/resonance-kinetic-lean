import Resonance.CornerConvolution
import Resonance.AxisDensityIntegrability
import Resonance.L2ConvolutionContinuity

/-! The explicit signed product-density convolution has a finite
continuous representative at every energy, including zero. -/
open Real Set MeasureTheory
open scoped ENNReal Topology
namespace Resonance.CornerConvolutionContinuity
noncomputable section
set_option maxHeartbeats 800000
open Resonance.AxisProductDensity Resonance.AxisDensityIntegrability
open Resonance.CornerConvolution Resonance.L2ConvolutionContinuity

def realSumDensity (d:Fin 3→ℝ) (E:ℝ) : ℝ :=
  ∫s:ℝ,(axisDensity (d 0) s).toReal*
    (∫t:ℝ,(axisDensity (d 1) t).toReal*(axisDensity (d 2) (E-s-t)).toReal)

theorem realSumDensity_nonneg (d:Fin 3→ℝ) (E:ℝ) : 0≤realSumDensity d E := by
  apply integral_nonneg
  intro s
  apply mul_nonneg ENNReal.toReal_nonneg
  apply integral_nonneg
  intro t
  exact mul_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg

theorem realSumDensity_continuous {d:Fin 3→ℝ}
    (hd0:∀i,0≤d i) (hd1:∀i,d i≤1) : Continuous (realSumDensity d) :=
  triple_convolution_continuous (axisDensity_real_integrable (hd0 0) (hd1 0))
    (axisDensity_real_memLp_two (hd0 1) (hd1 1))
    (axisDensity_real_memLp_two (hd0 2) (hd1 2))

theorem sumDensity_eq_ofReal {d:Fin 3→ℝ}
    (hd0:∀i,0≤d i) (hd1:∀i,d i≤1) (E:ℝ) :
    sumDensity d E=ENNReal.ofReal (realSumDensity d E) := by
  have h1 := axisDensity_real_memLp_two (hd0 1) (hd1 1)
  have h2 := axisDensity_real_memLp_two (hd0 2) (hd1 2)
  have hinn (s:ℝ) : ENNReal.ofReal (∫t:ℝ,(axisDensity (d 1) t).toReal*
        (axisDensity (d 2) (E-s-t)).toReal)=
      ∫⁻t:ℝ,axisDensity (d 1) t*axisDensity (d 2) (E-s-t) := by
    rw [ofReal_integral_eq_lintegral_ofReal (convolution_integrable h1 h2 (E-s))
      (ae_of_all _ (fun t=>mul_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg))]
    apply lintegral_congr
    intro t
    rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg,
      ENNReal.ofReal_toReal (axisDensity_finite _ _).ne,
      ENNReal.ofReal_toReal (axisDensity_finite _ _).ne]
  have hout := triple_convolution_integrable
    (axisDensity_real_integrable (hd0 0) (hd1 0)) h1 h2 E
  unfold realSumDensity
  have hp : 0≤ᵐ[(volume:Measure ℝ)] (fun s:ℝ=>(axisDensity (d 0) s).toReal*
      (∫t:ℝ,(axisDensity (d 1) t).toReal*(axisDensity (d 2) (E-s-t)).toReal)) := by
    apply ae_of_all
    intro s
    apply mul_nonneg ENNReal.toReal_nonneg
    exact integral_nonneg (fun t=>mul_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg)
  rw [ofReal_integral_eq_lintegral_ofReal hout hp]
  unfold sumDensity
  apply lintegral_congr
  intro s
  rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg,
    ENNReal.ofReal_toReal (axisDensity_finite _ _).ne,hinn s]
  have hm : Measurable (fun t:ℝ=>axisDensity (d 1) t*axisDensity (d 2) (E-s-t)) :=
    (axisDensity_measurable _).mul ((axisDensity_measurable _).comp (by fun_prop))
  rw [←lintegral_const_mul _ hm]
  apply lintegral_congr
  intro t
  ring

theorem sumDensity_finite {d:Fin 3→ℝ}
    (hd0:∀i,0≤d i) (hd1:∀i,d i≤1) (E:ℝ) : sumDensity d E<∞ := by
  rw [sumDensity_eq_ofReal hd0 hd1]
  exact ENNReal.ofReal_lt_top

theorem sumDensity_continuous {d:Fin 3→ℝ}
    (hd0:∀i,0≤d i) (hd1:∀i,d i≤1) : Continuous (sumDensity d) := by
  have he : sumDensity d=fun E=>ENNReal.ofReal (realSumDensity d E) :=
    funext (sumDensity_eq_ofReal hd0 hd1)
  rw [he]
  exact ENNReal.continuous_ofReal.comp (realSumDensity_continuous hd0 hd1)

end
end Resonance.CornerConvolutionContinuity
