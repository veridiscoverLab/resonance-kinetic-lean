import Resonance.ProfileParameterBounds

/-! Original five-moment analysis and synthesis on fixed Banach spaces.
Their parameter dependence is proved from the actual N times Psi. -/
open MeasureTheory Set
open scoped ENNReal BigOperators
namespace Resonance.BasisParameterContinuity
noncomputable section
set_option maxHeartbeats 1200000
open ResonantMeasure Thermodynamics WeightedJointMeasure ReferenceFrequencySpace
open PhysicalFiveBasis ReferenceMomentFunctionals LinftyFiveAugmentation ActualPairNormalization
open ProfileParameterBounds

theorem compact_basis_difference_bound {R : ℝ} (hR : 0≤R) {K : Set Parameter}
    (hK : IsCompact K) (hpos : K⊆positiveDomain R) :
    ∃C : ℝ,0≤C ∧ ∀θ∈K,∀β∈K,∀i : Fin 5,∀k∈cube R,
      ‖basisFunction θ i k-basisFunction β i k‖≤C*‖θ-β‖ := by
  obtain ⟨m,M,C,hm,hM,hC,hb,hd⟩ := compact_profile_lipschitz hR hK hpos
  let B := ∑i : Fin 5,‖invariantContinuous R i‖
  have hB : 0≤B := Finset.sum_nonneg (fun _ _=>norm_nonneg _)
  refine ⟨C*B,mul_nonneg hC hB,?_⟩
  intro θ hθ β hβ i k hk
  have hi : ‖CoareaNormalization.euclideanFive i k‖≤B :=
    ((invariantContinuous R i).norm_coe_le_norm ⟨k,hk⟩).trans
      (Finset.single_le_sum (fun j _=>norm_nonneg (invariantContinuous R j)) (Finset.mem_univ i))
  unfold basisFunction
  rw [←sub_mul,norm_mul,Real.norm_eq_abs]
  exact (mul_le_mul (hd θ hθ β hβ k hk) hi (norm_nonneg _) (by positivity)).trans_eq (by ring)

theorem moment_difference_bound {R : ℝ} (hR : 0<R) {ψ χ : E→ℝ}
    (hψ : MemLp ψ ∞ (referenceMeasure R)) (hχ : MemLp χ ∞ (referenceMeasure R))
    {D : ℝ} (hD : 0≤D) (hd : ∀ᵐ k∂referenceMeasure R,‖ψ k-χ k‖≤D) :
    ‖moment hR hψ-moment hR hχ‖≤‖totalMoment hR‖*D := by
  apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg (norm_nonneg _) hD)
  intro u
  change ‖totalMoment hR (LpOperators.multiplyCLM hψ u)-
    totalMoment hR (LpOperators.multiplyCLM hχ u)‖≤_
  rw [←map_sub]
  have hh : ‖LpOperators.multiplyCLM hψ u-LpOperators.multiplyCLM hχ u‖≤D*‖u‖ := by
    apply Lp.norm_le_mul_norm_of_ae_le_mul
    filter_upwards [LpOperators.multiply_ae hψ u,LpOperators.multiply_ae hχ u,
      Lp.coeFn_sub (LpOperators.multiplyCLM hψ u) (LpOperators.multiplyCLM hχ u),hd] with k h1 h2 hs hk
    simp only [Pi.sub_apply] at hs
    change (LpOperators.multiplyCLM hψ u) k=u k*ψ k at h1
    change (LpOperators.multiplyCLM hχ u) k=u k*χ k at h2
    rw [hs,h1,h2,←mul_sub,norm_mul]
    exact (mul_le_mul_of_nonneg_left hk (norm_nonneg _)).trans_eq (mul_comm _ _)
  exact ((totalMoment hR).le_opNorm _).trans
    ((mul_le_mul_of_nonneg_left hh (norm_nonneg _)).trans_eq (by ring))

theorem compact_analysis_difference_bound {R : ℝ} (hR : 0<R)
    {K : Set Parameter} (hK : IsCompact K) (hpos : K⊆positiveDomain R) :
    ∃C : ℝ,0≤C ∧ ∀(θ : Parameter)(hθ : θ∈K)(β : Parameter)(hβ : β∈K),
      ‖analysisMap hR (hpos hθ)-analysisMap hR (hpos hβ)‖≤C*‖θ-β‖ := by
  obtain ⟨C,hC,hb⟩ := compact_basis_difference_bound hR.le hK hpos
  refine ⟨‖totalMoment hR‖*C,by positivity,?_⟩
  intro θ hθ β hβ
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro u
  apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
  intro i
  have hd := moment_difference_bound hR (basis_memLp_top (hpos hθ) i)
    (basis_memLp_top (hpos hβ) i) (mul_nonneg hC (norm_nonneg (θ-β))) (by
      filter_upwards [reference_support R] with k hk
      exact hb θ hθ β hβ i k hk)
  have he := ((moment hR (basis_memLp_top (hpos hθ) i)-
    moment hR (basis_memLp_top (hpos hβ) i)).le_opNorm u).trans
      (mul_le_mul_of_nonneg_right hd (norm_nonneg u))
  exact he.trans_eq (by ring)

theorem compact_synthesis_difference_bound {R : ℝ} (hR : 0≤R)
    {K : Set Parameter} (hK : IsCompact K) (hpos : K⊆positiveDomain R) :
    ∃C : ℝ,0≤C ∧ ∀(θ : Parameter)(hθ : θ∈K)(β : Parameter)(hβ : β∈K),
      ‖synthesisTop (hpos hθ)-synthesisTop (hpos hβ)‖≤C*‖θ-β‖ := by
  obtain ⟨C,hC,hb⟩ := compact_basis_difference_bound hR hK hpos
  refine ⟨5*C,by positivity,?_⟩
  intro θ hθ β hβ
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro b
  change ‖CubeLinftyCoordinates.embed R (synthesisContinuous (hpos hθ) b)-
    CubeLinftyCoordinates.embed R (synthesisContinuous (hpos hβ) b)‖≤_
  rw [←map_sub]
  apply (CubeLinftyCoordinates.extendVector_bound R _).trans
  apply (ContinuousMap.norm_le _ (by positivity)).mpr
  intro k
  change ‖synthesisContinuous (hpos hθ) b k-synthesisContinuous (hpos hβ) b k‖≤_
  rw [synthesisContinuous_apply,synthesisContinuous_apply,←Finset.sum_sub_distrib]
  calc
    _ ≤ ∑i : Fin 5,‖b i*basisFunction θ i k-b i*basisFunction β i k‖ := norm_sum_le _ _
    _ ≤ ∑_i : Fin 5,‖b‖*(C*‖θ-β‖) := by
      apply Finset.sum_le_sum
      intro i _
      rw [←mul_sub,norm_mul]
      exact mul_le_mul (norm_le_pi_norm b i) (hb θ hθ β hβ i k k.property)
        (norm_nonneg _) (norm_nonneg _)
    _ = _ := by simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]; ring

end
end Resonance.BasisParameterContinuity
