import Resonance.PhysicalWeightedCoercivity

/-! The actual inverse reference frequency represents unweighted moments
on the manuscript's weighted space. Its zero-frequency corners are retained. -/
open MeasureTheory Set
open scoped ENNReal
namespace Resonance.ReferenceMomentFunctionals
noncomputable section
open ResonantMeasure CollisionFrequency ActualPairNormalization ReferenceFrequencySpace

theorem inverse_memLp {R : ℝ} (hR : 0<R) :
    MemLp (fun k=>(referenceFrequency R k)⁻¹) 2 (referenceMeasure R) := by
  have hm : Measurable (referenceFrequency R) :=
    CollisionMarginalDensity.lossFrequency_measurable R referenceProfile_continuous.measurable
  apply (memLp_two_iff_integrable_sq hm.inv.aestronglyMeasurable).mpr
  change Integrable _ ((cubeVolume R).withDensity _)
  apply (integrable_withDensity_iff_integrable_smul'
    (reference_density_measurable R) (ae_of_all _ fun _=>ENNReal.ofReal_lt_top)).mpr
  apply (CornerInverseFrequency.reference_inverse_integrable hR).congr
  filter_upwards [CornerInverseFrequency.referenceFrequency_positive_ae hR] with k hk
  simp only [ENNReal.toReal_ofReal hk.le,smul_eq_mul]
  field_simp

def inverseVector {R : ℝ} (hR : 0<R) : Space R := (inverse_memLp hR).toLp _

theorem inverseVector_ae {R : ℝ} (hR : 0<R) :
    (inverseVector hR : E→ℝ)=ᵐ[referenceMeasure R]
      (fun k=>(referenceFrequency R k)⁻¹) := (inverse_memLp hR).coeFn_toLp

theorem unweighted_integrable {R : ℝ} (hR : 0<R) (u : Space R) :
    Integrable (u : E→ℝ) (cubeVolume R) := by
  have hi : Integrable (fun k=>u k*(referenceFrequency R k)⁻¹) (referenceMeasure R) :=
    (Lp.memLp u).integrable_mul (inverse_memLp hR)
  have hh := (integrable_withDensity_iff_integrable_smul'
    (reference_density_measurable R) (ae_of_all (cubeVolume R) fun _=>ENNReal.ofReal_lt_top)).mp hi
  apply hh.congr
  filter_upwards [CornerInverseFrequency.referenceFrequency_positive_ae hR] with k hk
  simp only [ENNReal.toReal_ofReal hk.le,smul_eq_mul]
  field_simp

theorem integral_as_inner {R : ℝ} (hR : 0<R) (u : Space R) :
    (∫k,u k∂cubeVolume R)=inner ℝ (inverseVector hR) u := by
  rw [L2.inner_def]
  calc
    (∫k,u k∂cubeVolume R)=∫k,u k*(referenceFrequency R k)⁻¹∂referenceMeasure R := by
      change (∫k,u k∂cubeVolume R)=∫k,u k*(referenceFrequency R k)⁻¹
        ∂(cubeVolume R).withDensity (fun k=>ENNReal.ofReal (referenceFrequency R k))
      rw [integral_withDensity_eq_integral_toReal_smul
        (reference_density_measurable R) (ae_of_all _ fun _=>ENNReal.ofReal_lt_top)]
      apply integral_congr_ae
      filter_upwards [CornerInverseFrequency.referenceFrequency_positive_ae hR] with k hk
      simp only [ENNReal.toReal_ofReal hk.le,smul_eq_mul]
      field_simp
    _=_ := by
      apply integral_congr_ae
      filter_upwards [inverseVector_ae hR] with k hk
      change u k*(referenceFrequency R k)⁻¹=u k*inverseVector hR k
      rw [hk]

def totalMoment {R : ℝ} (hR : 0<R) : Space R→L[ℝ]ℝ := innerSL ℝ (inverseVector hR)

theorem totalMoment_apply {R : ℝ} (hR : 0<R) (u : Space R) :
    totalMoment hR u=∫k,u k∂cubeVolume R := (integral_as_inner hR u).symm

def moment {R : ℝ} (hR : 0<R) {ψ : E→ℝ}
    (hψ : MemLp ψ ∞ (referenceMeasure R)) : Space R→L[ℝ]ℝ :=
  (totalMoment hR).comp (LpOperators.multiplyCLM hψ)

theorem weighted_moment_integrable {R : ℝ} (hR : 0<R) {ψ : E→ℝ}
    (hψ : MemLp ψ ∞ (referenceMeasure R)) (u : Space R) :
    Integrable (fun k=>u k*ψ k) (cubeVolume R) := by
  apply (unweighted_integrable hR (LpOperators.multiplyCLM hψ u)).congr
  exact (reference_volume_equivalent hR).1.ae_eq (LpOperators.multiply_ae hψ u)

theorem moment_apply {R : ℝ} (hR : 0<R) {ψ : E→ℝ}
    (hψ : MemLp ψ ∞ (referenceMeasure R)) (u : Space R) :
    moment hR hψ u=∫k,u k*ψ k∂cubeVolume R := by
  rw [moment,ContinuousLinearMap.comp_apply,totalMoment_apply]
  apply integral_congr_ae
  exact (reference_volume_equivalent hR).1.ae_eq (LpOperators.multiply_ae hψ u)

end
end Resonance.ReferenceMomentFunctionals
