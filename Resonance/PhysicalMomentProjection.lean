import Resonance.PhysicalFiveBasis

/-! The actual unweighted five-moment projection, extended to H_nu by
proved inverse-frequency integrability and the actual thermodynamic Gram inverse. -/
open MeasureTheory Set
open scoped BigOperators
namespace Resonance.PhysicalMomentProjection
noncomputable section
open ResonantMeasure WeightedJointMeasure Thermodynamics ReferenceFrequencySpace
open PhysicalFiveBasis ReferenceMomentFunctionals ActualPairNormalization
open CoareaNormalization (euclideanFive)

theorem analysis_synthesis {R : ℝ} (hR : 0<R) {θ : Parameter}
    (hθ : θ∈positiveDomain R) (b : Parameter) :
    analysisMap hR hθ (synthesis hR.le hθ b)=(gramMatrix R θ).mulVec b := by
  funext i
  rw [analysisMap_apply]
  calc
    _ = ∫k,∑j : Fin 5,b j*(basisFunction θ i k*basisFunction θ j k)∂cubeVolume R := by
      apply integral_congr_ae
      filter_upwards [(reference_volume_equivalent hR).1.ae_eq (synthesis_ae hR.le hθ b)] with k hk
      rw [hk]
      simp only [Entropy.denominator,Finset.mul_sum,Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro j _
      unfold basisFunction
      ring
    _ = _ := by
      rw [integral_finset_sum Finset.univ
        (fun j _=>(basis_product_integrable hθ i j).const_mul (b j))]
      simp only [integral_const_mul,basis_gram hθ,Matrix.mulVec,dotProduct]
      apply Finset.sum_congr rfl
      intro j _
      exact mul_comm _ _

def gramInverse {R : ℝ} (hR : 0<R) {θ : Parameter}
    (hθ : θ∈positiveDomain R) : Parameter→L[ℝ]Parameter :=
  -(ThermodynamicChart.derivativeEquiv R hR θ hθ).symm.toContinuousLinearMap

theorem gramInverse_mulVec {R : ℝ} (hR : 0<R) {θ : Parameter}
    (hθ : θ∈positiveDomain R) (b : Parameter) :
    gramInverse hR hθ ((gramMatrix R θ).mulVec b)=b := by
  have hh := momentDerivative_apply R θ hθ b
  have he : (gramMatrix R θ).mulVec b=
      -(ThermodynamicChart.derivativeEquiv R hR θ hθ) b := by
    rw [←ContinuousLinearEquiv.coe_coe,ThermodynamicChart.derivativeEquiv_toCLM,hh,neg_neg]
  rw [he]
  simp only [gramInverse,ContinuousLinearMap.neg_apply,map_neg,
    ContinuousLinearEquiv.coe_coe,ContinuousLinearEquiv.symm_apply_apply,neg_neg]

theorem mulVec_gramInverse {R : ℝ} (hR : 0<R) {θ : Parameter}
    (hθ : θ∈positiveDomain R) (b : Parameter) :
    (gramMatrix R θ).mulVec (gramInverse hR hθ b)=b := by
  have hs : Function.Surjective (fun c=>(gramMatrix R θ).mulVec c) := by
    intro v
    refine ⟨(ThermodynamicChart.derivativeEquiv R hR θ hθ).symm (-v),?_⟩
    have hh := momentDerivative_apply R θ hθ
      ((ThermodynamicChart.derivativeEquiv R hR θ hθ).symm (-v))
    have he : momentDerivative R θ
        ((ThermodynamicChart.derivativeEquiv R hR θ hθ).symm (-v)) = -v := by
      rw [←ThermodynamicChart.derivativeEquiv_toCLM R hR θ hθ]
      exact (ThermodynamicChart.derivativeEquiv R hR θ hθ).apply_symm_apply (-v)
    rw [he] at hh
    exact neg_injective hh.symm
  obtain ⟨c,rfl⟩ := hs b
  rw [gramInverse_mulVec]

def projection {R : ℝ} (hR : 0<R) {θ : Parameter}
    (hθ : θ∈positiveDomain R) : Space R→L[ℝ]Space R :=
  (synthesis hR.le hθ).comp ((gramInverse hR hθ).comp (analysisMap hR hθ))

theorem projection_synthesis {R : ℝ} (hR : 0<R) {θ : Parameter}
    (hθ : θ∈positiveDomain R) (b : Parameter) :
    projection hR hθ (synthesis hR.le hθ b)=synthesis hR.le hθ b := by
  simp only [projection,ContinuousLinearMap.comp_apply,analysis_synthesis,gramInverse_mulVec]

theorem projection_idempotent {R : ℝ} (hR : 0<R) {θ : Parameter}
    (hθ : θ∈positiveDomain R) (u : Space R) :
    projection hR hθ (projection hR hθ u)=projection hR hθ u :=
  projection_synthesis hR hθ _

theorem projection_moments {R : ℝ} (hR : 0<R) {θ : Parameter}
    (hθ : θ∈positiveDomain R) (u : Space R) :
    analysisMap hR hθ (projection hR hθ u)=analysisMap hR hθ u := by
  change analysisMap hR hθ (synthesis hR.le hθ _)=_
  rw [analysis_synthesis]
  exact mulVec_gramInverse hR hθ (analysisMap hR hθ u)

theorem projection_residual_orthogonal {R : ℝ} (hR : 0<R) {θ : Parameter}
    (hθ : θ∈positiveDomain R) (u : Space R) (i : Fin 5) :
    (∫k,(u k-projection hR hθ u k)*basisFunction θ i k∂cubeVolume R)=0 := by
  have hh := congrFun (projection_moments hR hθ u) i
  rw [analysisMap_apply,analysisMap_apply] at hh
  simp only [sub_mul]
  rw [integral_sub (weighted_moment_integrable hR (basis_memLp_top hθ i) u)
    (weighted_moment_integrable hR (basis_memLp_top hθ i) (projection hR hθ u)),hh,sub_self]

theorem projection_range {R : ℝ} (hR : 0<R) {θ : Parameter}
    (hθ : θ∈positiveDomain R) :
    (projection hR hθ).range=(synthesis hR.le hθ).range := by
  ext u
  constructor
  · rintro ⟨v,rfl⟩
    exact ⟨gramInverse hR hθ (analysisMap hR hθ v),rfl⟩
  · rintro ⟨b,rfl⟩
    exact ⟨synthesis hR.le hθ b,projection_synthesis hR hθ b⟩

theorem synthesis_injective {R : ℝ} (hR : 0<R) {θ : Parameter}
    (hθ : θ∈positiveDomain R) : Function.Injective (synthesis hR.le hθ) := by
  intro a b hab
  have hh := congrArg (fun u=>gramInverse hR hθ (analysisMap hR hθ u)) hab
  simpa only [analysis_synthesis,gramInverse_mulVec] using hh

end
end Resonance.PhysicalMomentProjection
