import Resonance.BoundedMomentSum
import Resonance.PhysicalMomentProjection

/-! The unknown weighted Gram matrix in cur:gramrecovery is built from
the actual unweighted five moments and the same full H_nu multiplier.
Its quadratic form is the original volume integral, including all corners. -/
open Set MeasureTheory Matrix
open scoped ENNReal BigOperators
namespace Resonance.WeightedMomentGram
noncomputable section
open ResonantMeasure Thermodynamics ReferenceFrequencySpace ActualPairNormalization
open PhysicalFiveBasis PhysicalMomentProjection ReferenceMomentFunctionals LpOperators

def basisCombination (θ a : Parameter) (k : E) : ℝ := ∑ i : Fin 5,a i*basisFunction θ i k

theorem basisCombination_memLp {R : ℝ} {θ : Parameter} (hθ : θ∈positiveDomain R)
    (a : Parameter) : MemLp (basisCombination θ a) ∞ (referenceMeasure R) :=
  BoundedMomentSum.bounded_sum_memLp (basis_memLp_top hθ) a

theorem basisCombination_eq (θ a : Parameter) (k : E) :
    basisCombination θ a k=WeightedJointMeasure.profile θ k*
      Entropy.denominator CoareaNormalization.euclideanFive a k := by
  simp only [basisCombination,basisFunction,Entropy.denominator,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem synthesis_combination_ae {R : ℝ} (hR : 0 < R) {θ : Parameter}
    (hθ : θ∈positiveDomain R) (a : Parameter) :
    (synthesis hR.le hθ a : E→ℝ)=ᵐ[cubeVolume R] basisCombination θ a := by
  have h := (reference_volume_equivalent hR).1.ae_eq (synthesis_ae hR.le hθ a)
  filter_upwards [h] with k hk
  rw [basisCombination_eq]
  exact hk

theorem analysis_dot_integral {R : ℝ} (hR : 0 < R) {θ : Parameter}
    (hθ : θ∈positiveDomain R) (u : Space R) (a : Parameter) :
    a ⬝ᵥ analysisMap hR hθ u=∫ k,u k*basisCombination θ a k ∂cubeVolume R := by
  have h := congrArg (fun T : Space R→L[ℝ]ℝ=>T u)
    (BoundedMomentSum.moment_sum hR (basis_memLp_top hθ) a)
  dsimp only at h
  rw [moment_apply] at h
  simpa only [ContinuousLinearMap.sum_apply,ContinuousLinearMap.smul_apply,smul_eq_mul,
    dotProduct,analysisMap,ContinuousLinearMap.pi_apply] using h.symm

def weightedGram {R : ℝ} (hR : 0 < R) {θ : Parameter} (hθ : θ∈positiveDomain R)
    {b : E→ℝ} (hb : MemLp b ∞ (referenceMeasure R)) : Parameter→L[ℝ]Parameter :=
  (analysisMap hR hθ).comp ((multiplyCLM hb).comp (synthesis hR.le hθ))

theorem weighted_square_integrable {R : ℝ} (hR : 0 < R) {θ : Parameter}
    (hθ : θ∈positiveDomain R) {b : E→ℝ} (hb : MemLp b ∞ (referenceMeasure R))
    (a : Parameter) : Integrable (fun k=>b k*(basisCombination θ a k)^2) (cubeVolume R) := by
  have h := weighted_moment_integrable hR (basisCombination_memLp hθ a)
    (multiplyCLM hb (synthesis hR.le hθ a))
  apply h.congr
  filter_upwards [(reference_volume_equivalent hR).1.ae_eq
    (multiply_ae hb (synthesis hR.le hθ a)),synthesis_combination_ae hR hθ a] with k hk hs
  change multiply hb (synthesis hR.le hθ a) k*basisCombination θ a k=_
  rw [hk,hs]
  ring

theorem weightedGram_quadratic {R : ℝ} (hR : 0 < R) {θ : Parameter}
    (hθ : θ∈positiveDomain R) {b : E→ℝ} (hb : MemLp b ∞ (referenceMeasure R))
    (a : Parameter) :
    a ⬝ᵥ weightedGram hR hθ hb a=∫ k,b k*(basisCombination θ a k)^2 ∂cubeVolume R := by
  change a ⬝ᵥ analysisMap hR hθ (multiplyCLM hb (synthesis hR.le hθ a))=_
  rw [analysis_dot_integral]
  apply integral_congr_ae
  filter_upwards [(reference_volume_equivalent hR).1.ae_eq
    (multiply_ae hb (synthesis hR.le hθ a)),synthesis_combination_ae hR hθ a] with k hk hs
  change multiply hb (synthesis hR.le hθ a) k*basisCombination θ a k=_
  rw [hk,hs]
  ring

theorem basis_square_integrable {R : ℝ} (hR : 0 < R) {θ : Parameter}
    (hθ : θ∈positiveDomain R) (a : Parameter) :
    Integrable (fun k=>(basisCombination θ a k)^2) (cubeVolume R) := by
  have h := weighted_moment_integrable hR (basisCombination_memLp hθ a) (synthesis hR.le hθ a)
  apply h.congr
  filter_upwards [synthesis_combination_ae hR hθ a] with k hk
  rw [hk,pow_two]

theorem basis_square_gram {R : ℝ} (hR : 0 < R) {θ : Parameter}
    (hθ : θ∈positiveDomain R) (a : Parameter) :
    (∫ k,(basisCombination θ a k)^2 ∂cubeVolume R)=a ⬝ᵥ (gramMatrix R θ).mulVec a := by
  rw [←analysis_synthesis hR hθ a,analysis_dot_integral]
  apply integral_congr_ae
  filter_upwards [synthesis_combination_ae hR hθ a] with k hk
  rw [hk,pow_two]

theorem weightedGram_lower {R : ℝ} (hR : 0 < R) {θ : Parameter}
    (hθ : θ∈positiveDomain R) {b : E→ℝ} (hb : MemLp b ∞ (referenceMeasure R))
    {m : ℝ} (hm : ∀ᵐ k ∂cubeVolume R,m ≤ b k) (a : Parameter) :
    m*(a ⬝ᵥ (gramMatrix R θ).mulVec a) ≤ a ⬝ᵥ weightedGram hR hθ hb a := by
  rw [weightedGram_quadratic,←basis_square_gram hR hθ a,←integral_const_mul]
  apply integral_mono_ae ((basis_square_integrable hR hθ a).const_mul m)
    (weighted_square_integrable hR hθ hb a)
  filter_upwards [hm] with k hk
  exact mul_le_mul_of_nonneg_right hk (sq_nonneg _)

end
end Resonance.WeightedMomentGram
