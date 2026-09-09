import Resonance.PhysicalProjectionKernel
import Mathlib.Analysis.Normed.Ring.Units

/-! Uniform bounds for the actual unweighted microprojection over any
compact subset of the original positive RJ parameter domain. -/
open MeasureTheory Set
open scoped ENNReal
namespace Resonance.PhysicalProjectionUniform
noncomputable section
open ResonantMeasure WeightedJointMeasure Thermodynamics ReferenceFrequencySpace
open PhysicalFiveBasis PhysicalMomentProjection PhysicalFrequencyCoordinates
open PhysicalFrequencyBounds JointWeightComparison ActualPairNormalization

def inverseGramFunction (R : ℝ) (θ : Parameter) : Parameter→L[ℝ]Parameter :=
  -Ring.inverse (momentDerivative R θ)

theorem inverseGramFunction_eq {R : ℝ} (hR : 0<R) {θ : Parameter}
    (hθ : θ∈positiveDomain R) : inverseGramFunction R θ=gramInverse hR hθ := by
  unfold inverseGramFunction gramInverse
  rw [←ThermodynamicChart.derivativeEquiv_toCLM R hR θ hθ]
  have h := Ring.inverse_unit (ThermodynamicChart.derivativeEquiv R hR θ hθ).toUnit
  exact congrArg Neg.neg h

theorem inverseGramFunction_continuousOn {R : ℝ} (hR : 0<R) :
    ContinuousOn (inverseGramFunction R) (positiveDomain R) := by
  intro θ hθ
  have hInv := NormedRing.inverse_continuousAt (ThermodynamicChart.derivativeEquiv R hR θ hθ).toUnit
  have he : ((ThermodynamicChart.derivativeEquiv R hR θ hθ).toUnit : Parameter→L[ℝ]Parameter)=
      momentDerivative R θ := ThermodynamicChart.derivativeEquiv_toCLM R hR θ hθ
  rw [he] at hInv
  exact (hInv.comp (momentDerivative_continuousAt R θ hθ)).neg.continuousWithinAt

theorem compact_inverseGram_bound {R : ℝ} (hR : 0<R) {K : Set Parameter}
    (hK : IsCompact K) (hpos : K⊆positiveDomain R) :
    ∃C : ℝ,0≤C ∧ ∀θ,(hθ : θ∈K) → ‖gramInverse hR (hpos hθ)‖≤C := by
  obtain ⟨C,hC⟩ := hK.bddAbove_image ((inverseGramFunction_continuousOn hR).mono hpos).norm
  refine ⟨max C 0,le_max_right _ _,?_⟩
  intro θ hθ
  rw [←inverseGramFunction_eq hR (hpos hθ)]
  exact (hC ⟨θ,hθ,rfl⟩).trans (le_max_left _ _)

theorem synthesis_profile_factor {R : ℝ} (hR : 0≤R) {θ : Parameter}
    (hθ : θ∈positiveDomain R) (b : Parameter) :
    synthesis hR hθ b=LpOperators.multiplyCLM (profile_memLp_reference hθ)
      (synthesis hR (unitParameter_positive R) b) := by
  apply Lp.ext
  filter_upwards [synthesis_ae hR hθ b,synthesis_ae hR (unitParameter_positive R) b,
    LpOperators.multiply_ae (profile_memLp_reference hθ)
      (synthesis hR (unitParameter_positive R) b)] with k hk hu hm
  change (synthesis hR hθ b : E→ℝ) k=
    (LpOperators.multiply (profile_memLp_reference hθ)
      (synthesis hR (unitParameter_positive R) b) : E→ℝ) k
  rw [hk,hm,hu,unit_profile,one_mul,mul_comm]

theorem analysis_profile_factor {R : ℝ} (hR : 0<R) {θ : Parameter}
    (hθ : θ∈positiveDomain R) (u : Space R) :
    analysisMap hR hθ u=analysisMap hR (unitParameter_positive R)
      (LpOperators.multiplyCLM (profile_memLp_reference hθ) u) := by
  funext i
  rw [analysisMap_apply,analysisMap_apply]
  apply integral_congr_ae
  have he := (reference_volume_equivalent hR).1.ae_eq
    (LpOperators.multiply_ae (profile_memLp_reference hθ) u)
  filter_upwards [he] with k hk
  change u k*basisFunction θ i k=LpOperators.multiply (profile_memLp_reference hθ) u k*
    basisFunction unitParameter i k
  rw [hk]
  simp only [basisFunction,unit_profile,one_mul]
  ring

theorem projection_uniform_bound {R : ℝ} (hR : 0<R) {K : Set Parameter}
    (hK : IsCompact K) (hpos : K⊆positiveDomain R) :
    ∃C : ℝ,0≤C ∧ ∀θ,(hθ : θ∈K) → ∀u : Space R,
      ‖projection hR (hpos hθ) u‖≤C*‖u‖ := by
  obtain ⟨m,M,_hm,hM,hb⟩ := compact_profile_bounds hR.le hK hpos
  obtain ⟨G,hG,hGi⟩ := compact_inverseGram_bound hR hK hpos
  let S := synthesis hR.le (unitParameter_positive R)
  let A := analysisMap hR (unitParameter_positive R)
  refine ⟨M*‖S‖*G*‖A‖*M,by positivity,?_⟩
  intro θ hθ u
  have hmult (v : Space R) :
      ‖LpOperators.multiplyCLM (profile_memLp_reference (hpos hθ)) v‖≤M*‖v‖ := by
    apply multiply_explicit_bound (profile_memLp_reference (hpos hθ)) ?_ v
    filter_upwards [reference_support R] with k hk
    rw [Real.norm_eq_abs,abs_of_pos (profile_pos (hpos hθ) hk)]
    exact (hb θ hθ k hk).2
  change ‖synthesis hR.le (hpos hθ)
    (gramInverse hR (hpos hθ) (analysisMap hR (hpos hθ) u))‖≤_
  rw [synthesis_profile_factor,analysis_profile_factor]
  calc
    _ ≤ M*‖S (gramInverse hR (hpos hθ)
      (A (LpOperators.multiplyCLM (profile_memLp_reference (hpos hθ)) u)))‖ := hmult _
    _ ≤ M*(‖S‖*(G*(‖A‖*(M*‖u‖)))) := by
      gcongr
      exact (S.le_opNorm _).trans (mul_le_mul_of_nonneg_left
        ((ContinuousLinearMap.le_opNorm _ _).trans
          (mul_le_mul (hGi θ hθ)
            ((A.le_opNorm _).trans (mul_le_mul_of_nonneg_left (hmult u) (norm_nonneg A)))
            (norm_nonneg _) hG)) (norm_nonneg S))
    _ = _ := by ring

end
end Resonance.PhysicalProjectionUniform
