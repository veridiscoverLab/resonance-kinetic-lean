import Resonance.PhysicalMicroCoercivity

/-! Direct identification with the original unweighted L2 orthogonal
projection, rather than merely an abstract moment-preserving finite-rank map. -/
open MeasureTheory Set
open scoped ENNReal
namespace Resonance.UnweightedProjectionIdentity
noncomputable section
set_option maxHeartbeats 800000
open ResonantMeasure WeightedJointMeasure Thermodynamics ReferenceFrequencySpace
open PhysicalFiveBasis PhysicalMomentProjection PhysicalProjectionKernel
open PhysicalFrequencyCoordinates ActualPairNormalization

abbrev VolumeSpace (R : ℝ) := Lp ℝ 2 (cubeVolume R)

theorem reference_volume_domination {R : ℝ} (hR : 0≤R) :
    ∃C : ℝ≥0∞,C≠∞ ∧ referenceMeasure R≤C • cubeVolume R := by
  obtain ⟨C,hC⟩ := continuous_cube_bounded (CollisionFrequency.referenceFrequency_continuousOn hR)
  refine ⟨ENNReal.ofReal C,ENNReal.ofReal_ne_top,?_⟩
  change (cubeVolume R).withDensity _≤_
  rw [←withDensity_const]
  apply withDensity_mono
  filter_upwards [ae_restrict_mem (measurable_cube R)] with k hk
  exact ENNReal.ofReal_le_ofReal ((le_abs_self _).trans (hC k hk))

def embed {R : ℝ} (hR : 0≤R) : VolumeSpace R→L[ℝ]Space R :=
  LpOperators.changeCLM (Classical.choose_spec (reference_volume_domination hR)).1
    (Classical.choose_spec (reference_volume_domination hR)).2

theorem embed_ae {R : ℝ} (hR : 0≤R) (f : VolumeSpace R) :
    (embed hR f : E→ℝ)=ᵐ[referenceMeasure R] f :=
  LpOperators.changeMeasure_ae (Classical.choose_spec (reference_volume_domination hR)).1
    (Classical.choose_spec (reference_volume_domination hR)).2 f

theorem embed_volume_ae {R : ℝ} (hR : 0<R) (f : VolumeSpace R) :
    (embed hR.le f : E→ℝ)=ᵐ[cubeVolume R] f :=
  (reference_volume_equivalent hR).1.ae_eq (embed_ae hR.le f)

theorem basis_volume_memLp {R : ℝ} {θ : Parameter} (hθ : θ∈positiveDomain R) (i : Fin 5) :
    MemLp (basisFunction θ i) 2 (cubeVolume R) := by
  letI := cubeVolume_finite R
  obtain ⟨C,hC⟩ := continuous_cube_bounded (basis_continuousOn hθ i)
  apply MemLp.of_bound (basis_measurable θ i).aestronglyMeasurable C
  filter_upwards [ae_restrict_mem (measurable_cube R)] with k hk
  exact hC k hk

def volumeBasis {R : ℝ} {θ : Parameter} (hθ : θ∈positiveDomain R) (i : Fin 5) :
    VolumeSpace R := (basis_volume_memLp hθ i).toLp _

theorem volumeBasis_ae {R : ℝ} {θ : Parameter} (hθ : θ∈positiveDomain R) (i : Fin 5) :
    (volumeBasis hθ i : E→ℝ)=ᵐ[cubeVolume R] basisFunction θ i :=
  (basis_volume_memLp hθ i).coeFn_toLp

theorem volumeBasis_kernel {R : ℝ} (hR : 0<R) {θ : Parameter}
    (hθ : θ∈positiveDomain R) (i : Fin 5) :
    volumeBasis hθ i∈(WeightedOperator.operator hR.le hθ).ker := by
  apply (WeightedFiveKernel.actual_operator_kernel_iff hR hθ _).mpr
  refine ⟨parameterCoefficients (Pi.single i 1),?_⟩
  filter_upwards [volumeBasis_ae hθ i] with k hk
  exact hk.trans (by
    rw [parameterCoefficients_evaluate]
    simp [basisFunction,Entropy.denominator,Pi.single_apply,ite_mul])

theorem embedded_kernel {R : ℝ} (hR : 0<R) {θ : Parameter}
    (hθ : θ∈positiveDomain R) {f : VolumeSpace R}
    (hf : f∈(WeightedOperator.operator hR.le hθ).ker) :
    embed hR.le f∈(physicalDifference hR.le hθ).ker := by
  obtain ⟨b,hb⟩ := (WeightedFiveKernel.actual_operator_kernel_iff hR hθ f).mp hf
  apply (physical_kernel_iff_exists hR hθ _).mpr
  exact ⟨b,(embed_volume_ae hR f).trans hb⟩

theorem embedded_starProjection_moments {R : ℝ} (hR : 0<R) {θ : Parameter}
    (hθ : θ∈positiveDomain R) (f : VolumeSpace R) :
    analysisMap hR hθ (embed hR.le ((WeightedOperator.operator hR.le hθ).ker.starProjection f))=
      analysisMap hR hθ (embed hR.le f) := by
  let T : VolumeSpace R→L[ℝ]VolumeSpace R := WeightedOperator.operator hR.le hθ
  let K : Submodule ℝ (VolumeSpace R) := T.ker
  letI : CompleteSpace K := T.isClosed_ker.completeSpace_coe
  funext i
  have hh : inner ℝ (f-K.starProjection f) (volumeBasis hθ i)=0 :=
    K.starProjection_inner_eq_zero f (volumeBasis hθ i) (volumeBasis_kernel hR hθ i)
  rw [L2.inner_def] at hh
  have he : (∫k,(f k-K.starProjection f k)*basisFunction θ i k∂cubeVolume R)=0 := by
    calc
      _ = ∫k,inner ℝ ((f-K.starProjection f) k) (volumeBasis hθ i k)∂cubeVolume R := by
        apply integral_congr_ae
        filter_upwards [Lp.coeFn_sub f (K.starProjection f),volumeBasis_ae hθ i] with k hk hb
        change (f k-K.starProjection f k)*basisFunction θ i k=
          volumeBasis hθ i k*(f-K.starProjection f) k
        rw [hk,hb]
        change (f k-K.starProjection f k)*basisFunction θ i k=
          basisFunction θ i k*(f k-K.starProjection f k)
        ring
      _ = 0 := hh
  rw [analysisMap_apply,analysisMap_apply]
  have hfi : Integrable (fun k=>f k*basisFunction θ i k) (cubeVolume R) := by
    apply (ReferenceMomentFunctionals.weighted_moment_integrable hR (basis_memLp_top hθ i)
      (embed hR.le f)).congr
    exact (embed_volume_ae hR f).mul (Filter.EventuallyEq.rfl)
  have hpi : Integrable (fun k=>K.starProjection f k*basisFunction θ i k) (cubeVolume R) := by
    apply (ReferenceMomentFunctionals.weighted_moment_integrable hR (basis_memLp_top hθ i)
      (embed hR.le (K.starProjection f))).congr
    exact (embed_volume_ae hR (K.starProjection f)).mul (Filter.EventuallyEq.rfl)
  simp only [sub_mul] at he
  rw [integral_sub hfi hpi] at he
  calc
    _ = ∫k,K.starProjection f k*basisFunction θ i k∂cubeVolume R :=
      integral_congr_ae ((embed_volume_ae hR _).mul (Filter.EventuallyEq.rfl))
    _ = ∫k,f k*basisFunction θ i k∂cubeVolume R := (sub_eq_zero.mp he).symm
    _ = _ := integral_congr_ae ((embed_volume_ae hR f).mul (Filter.EventuallyEq.rfl)).symm

theorem projection_is_original_unweighted {R : ℝ} (hR : 0<R) {θ : Parameter}
    (hθ : θ∈positiveDomain R) (f : VolumeSpace R) :
    projection hR hθ (embed hR.le f)=
      embed hR.le ((WeightedOperator.operator hR.le hθ).ker.starProjection f) := by
  have hk := embedded_kernel hR hθ
    ((WeightedOperator.operator hR.le hθ).ker.starProjection_apply_mem f)
  rw [←projection_fixed_kernel hR hθ hk]
  change synthesis hR.le hθ (gramInverse hR hθ (analysisMap hR hθ (embed hR.le f)))=
    synthesis hR.le hθ (gramInverse hR hθ (analysisMap hR hθ _))
  rw [embedded_starProjection_moments]

end
end Resonance.UnweightedProjectionIdentity
