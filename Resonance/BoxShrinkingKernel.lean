import Resonance.ShrinkingKernel
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-! One actual auxiliary kernel for deriving the coarea symmetry from the
already proved arbitrary-kernel limit. No symmetry assumption is imposed on
the arbitrary kernels in the original regularization theorem. -/
open Set MeasureTheory
namespace Resonance.BoxShrinkingKernel
noncomputable section

def kernel (η q : ℝ) : ℝ := (2*η)⁻¹ * (Icc (-η) η).indicator (fun _=>1) q

theorem kernel_measurable (η : ℝ) : Measurable (kernel η) :=
  (measurable_const.indicator measurableSet_Icc).const_mul _

theorem kernel_nonneg {η : ℝ} (hη : 0<η) (q : ℝ) : 0≤kernel η q := by
  unfold kernel
  apply mul_nonneg (by positivity)
  exact indicator_nonneg (fun _ _=>by norm_num) q

theorem kernel_support {η q : ℝ} (hq : kernel η q≠0) : |q|≤η := by
  by_contra hn
  have hq' : q∉Icc (-η) η := fun h=>hn (abs_le.mpr h)
  exact hq (by simp [kernel,hq'])

theorem kernel_integrable (η : ℝ) : Integrable (kernel η) := by
  apply Integrable.const_mul
  have hC : (volume:Measure ℝ) (Icc (-η) η)≠⊤ := isCompact_Icc.measure_lt_top.ne
  exact (integrable_indicator_iff measurableSet_Icc).mpr
    (integrableOn_const (C:=(1:ℝ)) (μ:=volume) (s:=Icc (-η) η) hC)

theorem kernel_mass {η : ℝ} (hη : 0<η) : ∫q,kernel η q=1 := by
  simp only [kernel]
  rw [integral_const_mul,integral_indicator_const (1:ℝ) measurableSet_Icc]
  simp only [smul_eq_mul,mul_one,Measure.real,Real.volume_Icc,sub_neg_eq_add]
  rw [ENNReal.toReal_ofReal (by positivity)]
  have he : η+η=2*η := by ring
  rw [he,inv_mul_cancel₀ (by positivity)]

theorem kernel_neg (η q : ℝ) : kernel η (-q)=kernel η q := by
  have he : -q∈Icc (-η) η ↔ q∈Icc (-η) η := by constructor <;> rintro ⟨h1,h2⟩ <;> constructor <;> linarith
  simp only [kernel,indicator,he]

end
end Resonance.BoxShrinkingKernel
