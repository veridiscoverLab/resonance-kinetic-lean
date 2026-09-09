import Resonance.BoundedMicroProjection

/-! Finite combinations of the actual bounded drives, in the original
weighted function space and the unweighted integral duality. -/
open MeasureTheory Set
open scoped ENNReal BigOperators
namespace Resonance.BoundedMomentSum
noncomputable section
set_option maxHeartbeats 800000
open ResonantMeasure WeightedJointMeasure Thermodynamics ReferenceFrequencySpace
open ActualPairNormalization (cubeVolume)
open ReferenceMomentFunctionals PhysicalFiveBasis PhysicalMomentProjection
open BoundedCellSource

theorem bounded_sum_memLp {I : Type*} [Fintype I] {R : ℝ} {F : I→E→ℝ}
    (hF : ∀i,MemLp (F i) ∞ (referenceMeasure R)) (a : I→ℝ) :
    MemLp (fun k=>∑i,a i*F i k) ∞ (referenceMeasure R) := by
  simpa only [smul_eq_mul] using
    (memLp_finset_sum Finset.univ (fun i _=>(hF i).const_smul (a i)))

theorem boundedVector_sum {I : Type*} [Fintype I] {R : ℝ} (hR : 0<R) {F : I→E→ℝ}
    (hF : ∀i,MemLp (F i) ∞ (referenceMeasure R)) (a : I→ℝ) :
    boundedVector hR (bounded_sum_memLp hF a)=∑i,a i • boundedVector hR (hF i) := by
  apply Lp.ext
  have ha := ae_all_iff.mpr (fun i=>(bounded_memLp_two hR (hF i)).coeFn_toLp)
  have hm := ae_all_iff.mpr (fun i=>Lp.coeFn_smul (a i) (boundedVector hR (hF i)))
  filter_upwards [(bounded_memLp_two hR (bounded_sum_memLp hF a)).coeFn_toLp,
    finite_sum_ae Finset.univ (fun i=>a i • boundedVector hR (hF i)),ha,hm] with k hk hs ha hm
  change (boundedVector hR (bounded_sum_memLp hF a)) k=∑i,a i*F i k at hk
  rw [hk,hs]
  apply Finset.sum_congr rfl
  intro i _
  have hi : boundedVector hR (hF i) k=F i k := ha i
  rw [hm i]
  simp only [Pi.smul_apply,smul_eq_mul,hi]

theorem moment_sum {I : Type*} [Fintype I] {R : ℝ} (hR : 0<R) {F : I→E→ℝ}
    (hF : ∀i,MemLp (F i) ∞ (referenceMeasure R)) (a : I→ℝ) :
    moment hR (bounded_sum_memLp hF a)=∑i,a i • moment hR (hF i) := by
  apply ContinuousLinearMap.ext
  intro v
  rw [moment_apply]
  calc
    _ = ∫k,∑i,a i*(v k*F i k)∂cubeVolume R := by
      apply integral_congr_ae
      apply ae_of_all
      intro k
      change v k*(∑i,a i*F i k)=∑i,a i*(v k*F i k)
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = _ := by
      rw [integral_finset_sum Finset.univ
        (fun i _=>(weighted_moment_integrable hR (hF i) v).const_mul (a i))]
      simp only [integral_const_mul,ContinuousLinearMap.sum_apply,
        ContinuousLinearMap.smul_apply,smul_eq_mul,moment_apply]

theorem micro_sum {I : Type*} [Fintype I] {R : ℝ} (hR : 0<R) {θ : Parameter}
    (hθ : θ∈positiveDomain R) {F : I→E→ℝ}
    (hF : ∀i,MemLp (F i) ∞ (referenceMeasure R))
    (hQ : ∀i,projection hR hθ (boundedVector hR (hF i))=0) (a : I→ℝ) :
    projection hR hθ (boundedVector hR (bounded_sum_memLp hF a))=0 := by
  rw [boundedVector_sum hR hF a]
  simp only [map_sum,map_smul,hQ,smul_zero,Finset.sum_const_zero]

end
end Resonance.BoundedMomentSum
