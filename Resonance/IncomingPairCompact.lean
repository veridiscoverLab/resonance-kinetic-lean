import Resonance.MarginalInverseBounds
import Resonance.ActualCrossPairing

/-! Compactness of the actual incoming-pair term: the full pair density
is bounded, and the reciprocal of each actual marginal is integrable. -/
open MeasureTheory Set
open scoped ENNReal
namespace Resonance.IncomingPairCompact
noncomputable section
open ResonantMeasure WeightedJointMeasure ActualPairNormalization ActualPairKernels
open MarginalInverseBounds FrequencyWeightedForm FrequencyGramDecomposition

theorem bounded_pair_energy {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [SFinite μ] {a : X→ℝ≥0∞} {r : X×X→ℝ≥0∞}
    (ha : Measurable a) (hav : ∀ᵐx∂μ,a x≠0∧a x≠∞)
    (hai : (∫⁻x,(a x)⁻¹∂μ)<∞) {C : ℝ≥0∞} (hC : C≠∞)
    (hb : ∀ᵐp∂μ.prod μ,r p≤C) :
    (∫⁻p,(r p)^2/NormalizedPairDensity.productWeight a a p∂μ.prod μ)<∞ := by
  have hm : Measurable (fun p : X×X=>(a p.1)⁻¹*(a p.2)⁻¹) :=
    (ha.comp measurable_fst).inv.mul (ha.comp measurable_snd).inv
  have hprod : (∫⁻p : X×X,(a p.1)⁻¹*(a p.2)⁻¹∂μ.prod μ)=
      (∫⁻x,(a x)⁻¹∂μ)*(∫⁻x,(a x)⁻¹∂μ) := by
    rw [lintegral_prod _ hm.aemeasurable]
    simp_rw [lintegral_const_mul _ ha.inv]
    rw [lintegral_mul_const _ ha.inv]
  have hle : ∀ᵐp∂μ.prod μ,(r p)^2/NormalizedPairDensity.productWeight a a p ≤
      C^2*((a p.1)⁻¹*(a p.2)⁻¹) := by
    filter_upwards [hb,(Measure.quasiMeasurePreserving_fst (μ:=μ) (ν:=μ)).ae hav,
      (Measure.quasiMeasurePreserving_snd (μ:=μ) (ν:=μ)).ae hav] with p hp hp1 hp2
    dsimp [NormalizedPairDensity.productWeight]
    rw [div_eq_mul_inv,ENNReal.mul_inv (Or.inl hp1.1) (Or.inl hp1.2)]
    exact mul_le_mul' (pow_le_pow_left' hp 2) le_rfl
  apply lt_of_le_of_lt (lintegral_mono_ae hle)
  rw [lintegral_const_mul _ hm,hprod]
  exact ENNReal.mul_lt_top (ENNReal.pow_ne_top hC).lt_top (ENNReal.mul_lt_top hai hai)

theorem incoming_density_uniform_bound {R : ℝ} (hR : 0≤R)
    {θ : Thermodynamics.Parameter} (hθ : θ∈Thermodynamics.positiveDomain R) :
    ∃C : ℝ≥0∞,C≠∞ ∧ ∀p∈cube R×ˢcube R,IncomingPairDensity.density R (weight θ) p≤C := by
  obtain ⟨B,hB,hb⟩ := joint_weight_bounded hθ
  refine ⟨ENNReal.ofReal (6*R/8)*B*surface univ,
    (ENNReal.mul_lt_top (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hB.lt_top)
      (measure_lt_top surface univ)).ne,?_⟩
  intro p hp
  apply (IncomingPairDensity.density_bound R hb p).trans
  have hn : ‖p.1-p.2‖≤6*R := by
    have h1 := norm_le_three_R hR hp.1
    have h2 := norm_le_three_R hR hp.2
    exact (norm_sub_le _ _).trans (by linarith)
  exact mul_le_mul' (mul_le_mul'
    (ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_right hn (by norm_num))) le_rfl) le_rfl

theorem incoming_energy_finite {R : ℝ} (hR : 0<R)
    {θ : Thermodynamics.Parameter} (hθ : θ∈Thermodynamics.positiveDomain R) :
    (∫⁻p,(IncomingPairDensity.density R (weight θ) p)^2/
      NormalizedPairDensity.productWeight (marginalDensity R θ) (marginalDensity R θ) p
      ∂(cubeVolume R).prod (cubeVolume R))<∞ := by
  letI := cubeVolume_finite R
  obtain ⟨C,hC,hb⟩ := incoming_density_uniform_bound hR.le hθ
  apply bounded_pair_energy (cubeVolume R) (marginalDensity_measurable R θ)
    (marginalDensity_valid_ae hR hθ) (marginal_inverse_integral_finite hR hθ) hC
  filter_upwards [(Measure.quasiMeasurePreserving_fst (μ:=cubeVolume R) (ν:=cubeVolume R)).ae
      (ae_restrict_mem (measurable_cube R)),
    (Measure.quasiMeasurePreserving_snd (μ:=cubeVolume R) (ν:=cubeVolume R)).ae
      (ae_restrict_mem (measurable_cube R))] with p h1 h2
  exact hb p ⟨h1,h2⟩

theorem incoming_kernel_memLp {R : ℝ} (hR : 0<R)
    {θ : Thermodynamics.Parameter} (hθ : θ∈Thermodynamics.positiveDomain R) :
    MemLp (kernel01 R θ) 2 ((marginal R θ).prod (marginal R θ)) := by
  letI := cubeVolume_finite R
  rw [marginal_cube_density hR.le θ]
  exact NormalizedPairDensity.realKernel_memLp_of_energy (cubeVolume R) (cubeVolume R)
    (marginalDensity_measurable R θ) (marginalDensity_measurable R θ)
    (IncomingPairDensity.density_measurable R (weight_measurable θ))
    (marginalDensity_valid_ae hR hθ) (marginalDensity_valid_ae hR hθ)
    (incoming_energy_finite hR hθ)

theorem actual_cross01_compact {R : ℝ} (hR : 0<R)
    {θ : Thermodynamics.Parameter} (hθ : θ∈Thermodynamics.positiveDomain R) :
    IsCompactOperator (cross R θ 0 1) :=
  ActualCrossPairing.cross01_compact_of_kernel_memLp hR hθ (incoming_kernel_memLp hR hθ)

end
end Resonance.IncomingPairCompact
