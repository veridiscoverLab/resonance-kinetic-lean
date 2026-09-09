import Resonance.PinnedCompactGraph
import Mathlib.MeasureTheory.Integral.MeanInequalities

/-! Defect control uses the square of the complete original four-leg
difference.  Cauchy--Schwarz is applied before integration over the target;
the three source legs are not assigned independent collision energies. -/
open Real MeasureTheory Set Filter
open scoped ENNReal NNReal Topology
namespace Resonance.PinnedAverageDefect
noncomputable section

theorem enorm_integral_sq_le {Z : Type*} [MeasurableSpace Z] (μ : Measure Z)
    {F : Z→ℂ} (hF : AEStronglyMeasurable F μ) :
    ‖∫ z, F z ∂μ‖ₑ^2 ≤ (∫⁻ z, ‖F z‖ₑ^2 ∂μ)*μ univ := by
  have hh := ENNReal.lintegral_mul_le_Lp_mul_Lq μ
    (p:=2) (q:=2) (g:=fun _ => 1) (by norm_num [Real.holderConjugate_iff])
    hF.enorm aemeasurable_const
  have hcs : (∫⁻ z, ‖F z‖ₑ ∂μ) ≤
      (∫⁻ z, ‖F z‖ₑ^2 ∂μ)^(1/(2:ℝ)) * (μ univ)^(1/(2:ℝ)) := by
    have hpow (z : Z) : ‖F z‖ₑ^(2:ℝ) = ‖F z‖ₑ^(2:ℕ) := ENNReal.rpow_natCast _ 2
    simp_rw [hpow] at hh
    simpa only [Pi.mul_apply, mul_one, ENNReal.one_rpow, lintegral_const, one_mul,
      ENNReal.rpow_natCast] using hh
  have hs := pow_le_pow_left' hcs 2
  rw [mul_pow, ← ENNReal.rpow_mul_natCast, ← ENNReal.rpow_mul_natCast] at hs
  norm_num only at hs
  exact (pow_le_pow_left' (enorm_integral_le_lintegral_enorm F) 2).trans
    (by simpa only [ENNReal.rpow_one] using hs)

/-- The mean of the original complete difference is exactly the error of
the same three-source average.  All Bochner integrals are proved integrable
before this identity is used. -/
theorem source_average_defect_identity
    {Z : Type*} [MeasurableSpace Z] {μ : Measure Z}
    (v : ℂ) {χ : Z→ℝ} (hχ : Integrable χ μ) (hχone : ∫ z, χ z ∂μ = 1)
    {u₁ u₂ u₃ : Z→ℂ}
    (h₁ : Integrable (fun z => χ z • u₁ z) μ)
    (h₂ : Integrable (fun z => χ z • u₂ z) μ)
    (h₃ : Integrable (fun z => χ z • u₃ z) μ) :
    v-(∫ z, χ z • (u₁ z+u₂ z-u₃ z) ∂μ) =
      ∫ z, χ z • (v+u₃ z-u₁ z-u₂ z) ∂μ := by
  have hA : Integrable (fun z => χ z • (u₁ z+u₂ z-u₃ z)) μ := by
    simpa only [Pi.add_apply, Pi.sub_apply, Complex.real_smul, mul_add, mul_sub]
      using (h₁.add h₂).sub h₃
  have he : (fun z => χ z • (v+u₃ z-u₁ z-u₂ z)) =
      (fun z => χ z • v - χ z • (u₁ z+u₂ z-u₃ z)) := by
    funext z
    simp only [Complex.real_smul]
    ring
  rw [he]
  have hh := integral_sub (hχ.smul_const v) hA
  rw [integral_smul_const,hχone,one_smul] at hh
  exact hh.symm

theorem source_average_defect_sq_le
    {Z : Type*} [MeasurableSpace Z] {μ : Measure Z}
    (v : ℂ) {χ : Z→ℝ} (hχ : Integrable χ μ) (hχone : ∫ z, χ z ∂μ = 1)
    {u₁ u₂ u₃ : Z→ℂ}
    (h₁ : Integrable (fun z => χ z • u₁ z) μ)
    (h₂ : Integrable (fun z => χ z • u₂ z) μ)
    (h₃ : Integrable (fun z => χ z • u₃ z) μ)
    {B : ℝ} (hB : ∀ᵐ z∂μ, ‖χ z‖ ≤ B) :
    ‖v-(∫ z, χ z • (u₁ z+u₂ z-u₃ z) ∂μ)‖ₑ^2 ≤
      ((ENNReal.ofReal B)^2*μ univ) *
        (∫⁻ z, ‖v+u₃ z-u₁ z-u₂ z‖ₑ^2 ∂μ) := by
  rw [source_average_defect_identity v hχ hχone h₁ h₂ h₃]
  have hF : Integrable (fun z => χ z • (v+u₃ z-u₁ z-u₂ z)) μ := by
    simpa only [Pi.add_apply, Pi.sub_apply, Complex.real_smul, mul_add, mul_sub]
      using (((hχ.smul_const v).add h₃).sub h₁).sub h₂
  apply (enorm_integral_sq_le μ hF.aestronglyMeasurable).trans
  have hpoint : ∀ᵐ z∂μ, ‖χ z • (v+u₃ z-u₁ z-u₂ z)‖ₑ^2 ≤
      (ENNReal.ofReal B)^2*‖v+u₃ z-u₁ z-u₂ z‖ₑ^2 := by
    filter_upwards [hB] with z hz
    have he : ‖χ z • (v+u₃ z-u₁ z-u₂ z)‖ₑ ≤
        ENNReal.ofReal B*‖v+u₃ z-u₁ z-u₂ z‖ₑ := by
      calc
        _ = ENNReal.ofReal ‖χ z • (v+u₃ z-u₁ z-u₂ z)‖ := (ofReal_norm _).symm
        _ ≤ ENNReal.ofReal (‖χ z‖*‖v+u₃ z-u₁ z-u₂ z‖) :=
          ENNReal.ofReal_le_ofReal (norm_smul_le _ _)
        _ = ENNReal.ofReal ‖χ z‖*‖v+u₃ z-u₁ z-u₂ z‖ₑ := by
          simp only [ENNReal.ofReal_mul (norm_nonneg _),ofReal_norm]
        _ ≤ _ := mul_le_mul_left (ENNReal.ofReal_le_ofReal hz) _
    simpa only [mul_pow] using pow_le_pow_left' he 2
  calc
    _ ≤ ((∫⁻ z, (ENNReal.ofReal B)^2*‖v+u₃ z-u₁ z-u₂ z‖ₑ^2 ∂μ)*μ univ) := by
      exact mul_le_mul_left (lintegral_mono_ae hpoint) _
    _ = _ := by
      rw [lintegral_const_mul' _ _ (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)]
      ac_rfl

end
end Resonance.PinnedAverageDefect
