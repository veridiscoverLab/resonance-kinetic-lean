import Mathlib.Analysis.Convolution
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousCompMeasurePreserving
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Haar.Unique

/-! Continuity of the actual convolution of two L² functions on the
real line, proved through the continuous measure-preserving action on
the real L² Hilbert space. -/
open Set MeasureTheory
open scoped ENNReal Topology
namespace Resonance.L2ConvolutionContinuity
noncomputable section
set_option maxHeartbeats 600000

def reflectedTranslation (x:ℝ) : C(ℝ,ℝ) := ⟨fun t=>x-t,by fun_prop⟩

theorem reflectedTranslation_preserving (x:ℝ) :
    MeasurePreserving (reflectedTranslation x) volume volume :=
  (measurePreserving_add_left (volume:Measure ℝ) x).comp
    (Measure.measurePreserving_neg (volume:Measure ℝ))

theorem reflectedTranslation_continuous : Continuous reflectedTranslation := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  change Continuous (fun p:ℝ×ℝ=>p.1-p.2)
  fun_prop

theorem convolution_integrable {b c:ℝ→ℝ} (hb:MemLp b 2 volume) (hc:MemLp c 2 volume) (x:ℝ) :
    Integrable (fun t:ℝ=>b t*c (x-t)) volume :=
  hb.integrable_mul (hc.comp_measurePreserving (reflectedTranslation_preserving x))

theorem convolution_eq_inner {b c:ℝ→ℝ} (hb:MemLp b 2 volume) (hc:MemLp c 2 volume) (x:ℝ) :
    (∫t:ℝ,b t*c (x-t))=inner ℝ (hb.toLp b)
      (Lp.compMeasurePreserving (reflectedTranslation x) (reflectedTranslation_preserving x)
        (hc.toLp c)) := by
  rw [L2.inner_def]
  apply integral_congr_ae
  have hpull := (reflectedTranslation_preserving x).quasiMeasurePreserving.ae hc.coeFn_toLp
  filter_upwards [hb.coeFn_toLp,
    Lp.coeFn_compMeasurePreserving (hc.toLp c) (reflectedTranslation_preserving x),hpull]
    with t ht hu hv
  change b t*c (x-t)=
    (Lp.compMeasurePreserving (reflectedTranslation x) (reflectedTranslation_preserving x)
      (hc.toLp c)) t*(hb.toLp b) t
  rw [ht,hu,Function.comp_apply,hv]
  change b t*c (x-t)=c (x-t)*b t
  ring

theorem convolution_continuous {b c:ℝ→ℝ} (hb:MemLp b 2 volume) (hc:MemLp c 2 volume) :
    Continuous (fun x:ℝ=>∫t:ℝ,b t*c (x-t)) := by
  have hh : Continuous (fun x:ℝ=>
      Lp.compMeasurePreserving (reflectedTranslation x) (reflectedTranslation_preserving x)
        (hc.toLp c)) :=
    continuous_const.compMeasurePreservingLp reflectedTranslation_continuous
      reflectedTranslation_preserving (by norm_num)
  have he : (fun x:ℝ=>∫t:ℝ,b t*c (x-t))=
      fun x=>inner ℝ (hb.toLp b) (Lp.compMeasurePreserving (reflectedTranslation x)
        (reflectedTranslation_preserving x) (hc.toLp c)) :=
    funext (convolution_eq_inner hb hc)
  rw [he]
  exact continuous_const.inner hh

theorem convolution_bddAbove {b c:ℝ→ℝ} (hb:MemLp b 2 volume) (hc:MemLp c 2 volume) :
    BddAbove (range (fun x:ℝ=>‖∫t:ℝ,b t*c (x-t)‖)) := by
  refine ⟨‖hb.toLp b‖*‖hc.toLp c‖,?_⟩
  rintro _ ⟨x,rfl⟩
  dsimp only
  rw [convolution_eq_inner hb hc]
  simpa only [Lp.norm_compMeasurePreserving] using norm_inner_le_norm (hb.toLp b)
    (Lp.compMeasurePreserving (reflectedTranslation x) (reflectedTranslation_preserving x)
      (hc.toLp c))

theorem triple_convolution_continuous {a b c:ℝ→ℝ}
    (ha:Integrable a volume) (hb:MemLp b 2 volume) (hc:MemLp c 2 volume) :
    Continuous (fun E:ℝ=>∫s:ℝ,a s*(∫t:ℝ,b t*c (E-s-t))) := by
  exact (convolution_bddAbove hb hc).continuous_convolution_right_of_integrable
    (ContinuousLinearMap.mul ℝ ℝ) ha (convolution_continuous hb hc)

theorem triple_convolution_integrable {a b c:ℝ→ℝ}
    (ha:Integrable a volume) (hb:MemLp b 2 volume) (hc:MemLp c 2 volume) (E:ℝ) :
    Integrable (fun s:ℝ=>a s*(∫t:ℝ,b t*c (E-s-t))) volume := by
  obtain ⟨B,hB⟩ := convolution_bddAbove hb hc
  apply (ha.norm.mul_const B).mono'
    (ha.aestronglyMeasurable.mul
      (((convolution_continuous hb hc).comp (by fun_prop)).aestronglyMeasurable))
  apply ae_of_all
  intro s
  change ‖a s*(∫t:ℝ,b t*c (E-s-t))‖≤‖a s‖*B
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left (hB ⟨E-s,rfl⟩) (norm_nonneg _)

end
end Resonance.L2ConvolutionContinuity
