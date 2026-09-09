import Resonance.IncomingPairCompact
import Resonance.CornerNewtonEnergy

/-! The original incoming-outgoing pair kernel is square integrable in
the actual marginal product, including the full corner degeneration. -/
open MeasureTheory Set
open scoped ENNReal
namespace Resonance.CrossPairCompact
noncomputable section
open ResonantMeasure WeightedJointMeasure ActualPairNormalization ActualPairKernels
open MarginalInverseBounds FrequencyWeightedForm FrequencyGramDecomposition
open NewtonKernelBalls

theorem cross_density_square_bound {R : ℝ} (hR : 0≤R)
    {θ : Thermodynamics.Parameter} (hθ : θ∈Thermodynamics.positiveDomain R) :
    ∃C : ℝ≥0∞,C≠∞ ∧ ∀p : E×E,
      (CrossPairDensity.density R (weight θ) p)^2≤C*kernelTwo (p.2-p.1) := by
  obtain ⟨B,hB,hb⟩ := joint_weight_bounded hθ
  let C : ℝ≥0∞ := (1/2)*B*(volume : Measure PlaneCoarea.E2) (Metric.closedBall 0 (6*R))
  have hC : C≠∞ := (ENNReal.mul_lt_top
    (ENNReal.mul_lt_top (by norm_num) hB.lt_top)
    (isCompact_closedBall (0 : PlaneCoarea.E2) (6*R)).measure_lt_top).ne
  refine ⟨C^2,ENNReal.pow_ne_top hC,?_⟩
  intro p
  have hb1 : CrossPairDensity.density R (weight θ) p≤
      C*ENNReal.ofReal (‖p.2-p.1‖⁻¹) := by
    apply (CrossPairDensity.density_bound hR hb p).trans_eq
    dsimp [C]
    ring
  apply (pow_le_pow_left' hb1 2).trans_eq
  rw [mul_pow,←ENNReal.ofReal_pow (inv_nonneg.mpr (norm_nonneg _))]
  rfl

theorem cross_energy_finite {R : ℝ} (hR : 0<R)
    {θ : Thermodynamics.Parameter} (hθ : θ∈Thermodynamics.positiveDomain R) :
    (∫⁻p,(CrossPairDensity.density R (weight θ) p)^2/
      NormalizedPairDensity.productWeight (marginalDensity R θ) (marginalDensity R θ) p
      ∂(cubeVolume R).prod (cubeVolume R))<∞ := by
  letI := cubeVolume_finite R
  obtain ⟨C,hC,hb⟩ := cross_density_square_bound hR.le hθ
  obtain ⟨A,hA,ha⟩ := marginal_inverse_reference_bound hR hθ
  have hm : Measurable (fun p : E×E=>referenceInverse R p.1*referenceInverse R p.2*
      kernelTwo (p.2-p.1)) :=
    ((referenceInverse_measurable R).comp measurable_fst).mul
      ((referenceInverse_measurable R).comp measurable_snd) |>.mul
        (kernelTwo_measurable.comp (measurable_snd.sub measurable_fst))
  have hle : ∀ᵐp∂(cubeVolume R).prod (cubeVolume R),
      (CrossPairDensity.density R (weight θ) p)^2/
        NormalizedPairDensity.productWeight (marginalDensity R θ) (marginalDensity R θ) p ≤
      (C*A^2)*(referenceInverse R p.1*referenceInverse R p.2*kernelTwo (p.2-p.1)) := by
    filter_upwards [
      (Measure.quasiMeasurePreserving_fst (μ:=cubeVolume R) (ν:=cubeVolume R)).ae ha,
      (Measure.quasiMeasurePreserving_snd (μ:=cubeVolume R) (ν:=cubeVolume R)).ae ha,
      (Measure.quasiMeasurePreserving_fst (μ:=cubeVolume R) (ν:=cubeVolume R)).ae
        (marginalDensity_valid_ae hR hθ)] with p h1 h2 hv
    dsimp [NormalizedPairDensity.productWeight]
    rw [div_eq_mul_inv,ENNReal.mul_inv (Or.inl hv.1) (Or.inl hv.2)]
    calc
      _ ≤ (C*kernelTwo (p.2-p.1))*
          ((A*referenceInverse R p.1)*(A*referenceInverse R p.2)) :=
        mul_le_mul' (hb p) (mul_le_mul' h1 h2)
      _ = _ := by ring
  apply lt_of_le_of_lt (lintegral_mono_ae hle)
  rw [lintegral_const_mul _ hm]
  exact ENNReal.mul_lt_top (ENNReal.mul_lt_top hC.lt_top (ENNReal.pow_ne_top hA).lt_top)
    (CornerNewtonEnergy.reference_newton_energy_finite hR)

theorem cross_kernel_memLp {R : ℝ} (hR : 0<R)
    {θ : Thermodynamics.Parameter} (hθ : θ∈Thermodynamics.positiveDomain R) :
    MemLp (kernel02 R θ) 2 ((marginal R θ).prod (marginal R θ)) := by
  letI := cubeVolume_finite R
  rw [marginal_cube_density hR.le θ]
  exact NormalizedPairDensity.realKernel_memLp_of_energy (cubeVolume R) (cubeVolume R)
    (marginalDensity_measurable R θ) (marginalDensity_measurable R θ)
    (CrossPairDensity.density_measurable R (weight_measurable θ))
    (marginalDensity_valid_ae hR hθ) (marginalDensity_valid_ae hR hθ)
    (cross_energy_finite hR hθ)

theorem actual_cross02_compact {R : ℝ} (hR : 0<R)
    {θ : Thermodynamics.Parameter} (hθ : θ∈Thermodynamics.positiveDomain R) :
    IsCompactOperator (cross R θ 0 2) :=
  ActualCrossPairing.cross02_compact_of_kernel_memLp hR hθ (cross_kernel_memLp hR hθ)

end
end Resonance.CrossPairCompact
