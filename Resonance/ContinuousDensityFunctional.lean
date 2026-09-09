import Resonance.ContinuousTestUniqueness
import Mathlib.Topology.ContinuousMap.Compact

/-! The actual L¹ pairing defines a bounded linear functional on continuous
tests. All product integrals are justified by the uniform test norm. -/
open Set MeasureTheory Filter
namespace Resonance.ContinuousDensityFunctional
noncomputable section
variable {Y : Type*} [TopologicalSpace Y] [CompactSpace Y] [MeasurableSpace Y] [BorelSpace Y]

theorem test_integrable (μ : Measure Y) {f : Y→ℂ} (hf : Integrable f μ) (ψ : C(Y,ℂ)) :
    Integrable (fun y=>ψ y*f y) μ := by
  apply (hf.norm.const_mul ‖ψ‖).mono' (ψ.continuous.aestronglyMeasurable.mul hf.aestronglyMeasurable)
  filter_upwards [] with y
  change ‖ψ y*f y‖≤‖ψ‖*‖f y‖
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_right (ContinuousMap.norm_coe_le_norm ψ y) (norm_nonneg _)

theorem test_bound (μ : Measure Y) {f : Y→ℂ} (hf : Integrable f μ) (ψ : C(Y,ℂ)) :
    ‖∫y,ψ y*f y ∂μ‖≤(∫y,‖f y‖∂μ)*‖ψ‖ := by
  calc
    _ ≤ ∫y,‖ψ y*f y‖∂μ := norm_integral_le_integral_norm _
    _ ≤ ∫y,‖ψ‖*‖f y‖∂μ := integral_mono_ae (test_integrable μ hf ψ).norm
      (hf.norm.const_mul ‖ψ‖) (Eventually.of_forall (fun y=>by
        change ‖ψ y*f y‖≤‖ψ‖*‖f y‖
        rw [norm_mul]; exact mul_le_mul_of_nonneg_right (ContinuousMap.norm_coe_le_norm ψ y) (norm_nonneg _)))
    _ = _ := by rw [integral_const_mul]; ring

def functional (μ : Measure Y) {f : Y→ℂ} (hf : Integrable f μ) : C(Y,ℂ) →L[ℂ] ℂ :=
  LinearMap.mkContinuous
    { toFun := fun ψ=>∫y,ψ y*f y ∂μ
      map_add' := by
        intro ψ χ
        calc
          _ = ∫y,ψ y*f y+χ y*f y∂μ := integral_congr_ae (Eventually.of_forall (fun _=>by simp [add_mul]))
          _ = _ := integral_add (test_integrable μ hf ψ) (test_integrable μ hf χ)
      map_smul' := by
        intro c ψ
        calc
          _ = ∫y,c*(ψ y*f y)∂μ := integral_congr_ae (Eventually.of_forall (fun _=>by simp [mul_assoc]))
          _ = _ := integral_const_mul _ _ }
    (∫y,‖f y‖∂μ) (test_bound μ hf)

theorem functional_apply (μ : Measure Y) {f : Y→ℂ} (hf : Integrable f μ) (ψ : C(Y,ℂ)) :
    functional μ hf ψ=∫y,ψ y*f y∂μ := rfl

end
end Resonance.ContinuousDensityFunctional
