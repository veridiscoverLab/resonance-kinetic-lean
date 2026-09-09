import Resonance.StrongBoundedCell

/-! Fixed source embeddings and moment functionals for the original cube
L-infinity space. All representatives and integrals use the original measures. -/
open MeasureTheory
open scoped ENNReal
namespace Resonance.BoundedSourceMaps
noncomputable section
open ResonantMeasure Thermodynamics ReferenceFrequencySpace ActualPairNormalization
open PhysicalFiveBasis ReferenceMomentFunctionals StrongBoundedCell

theorem sourceVector_ae {R : ℝ} (hR : 0<R) (F : Lp ℝ ∞ (cubeVolume R)) :
    (sourceVector hR F : E→ℝ)=ᵐ[cubeVolume R] F :=
  BoundedCellSource.boundedVector_ae hR _

theorem sourceVector_add {R : ℝ} (hR : 0<R) (F G : Lp ℝ ∞ (cubeVolume R)) :
    sourceVector hR (F+G)=sourceVector hR F+sourceVector hR G := by
  apply Lp.ext
  apply (reference_volume_equivalent hR).2.ae_eq
  filter_upwards [sourceVector_ae hR (F+G),sourceVector_ae hR F,sourceVector_ae hR G,
    Lp.coeFn_add F G,(reference_volume_equivalent hR).1.ae_eq
      (Lp.coeFn_add (sourceVector hR F) (sourceVector hR G))] with k hfg hf hg hin hout
  simp only [Pi.add_apply] at hin hout
  rw [hfg,hout,hin,hf,hg]

theorem sourceVector_smul {R : ℝ} (hR : 0<R) (a : ℝ) (F : Lp ℝ ∞ (cubeVolume R)) :
    sourceVector hR (a • F)=a • sourceVector hR F := by
  apply Lp.ext
  apply (reference_volume_equivalent hR).2.ae_eq
  filter_upwards [sourceVector_ae hR (a • F),sourceVector_ae hR F,Lp.coeFn_smul a F,
    (reference_volume_equivalent hR).1.ae_eq (Lp.coeFn_smul a (sourceVector hR F))]
      with k haf hf hin hout
  simp only [Pi.smul_apply,smul_eq_mul] at hin hout
  rw [haf,hout,hin,hf]

def constantVector {R : ℝ} (hR : 0<R) : Space R :=
  basisVector hR.le (JointWeightComparison.unitParameter_positive R) 0

theorem constantVector_ae {R : ℝ} (hR : 0<R) :
    (constantVector hR : E→ℝ)=ᵐ[referenceMeasure R] (fun _=>1) := by
  filter_upwards [basisVector_ae hR.le (JointWeightComparison.unitParameter_positive R) 0] with k hk
  change basisVector hR.le (JointWeightComparison.unitParameter_positive R) 0 k=1
  rw [hk]
  simp [basisFunction,JointWeightComparison.unit_profile,CoareaNormalization.euclideanFive]

theorem sourceVector_as_multiplier {R : ℝ} (hR : 0<R) (F : Lp ℝ ∞ (cubeVolume R)) :
    sourceVector hR F=LpOperators.multiply (source_memLp_reference hR F) (constantVector hR) := by
  apply Lp.ext
  filter_upwards [(reference_volume_equivalent hR).2.ae_eq (sourceVector_ae hR F),
    LpOperators.multiply_ae (source_memLp_reference hR F) (constantVector hR),constantVector_ae hR]
      with k hf hm ho
  rw [hf,hm,ho,one_mul]

theorem sourceVector_bound {R : ℝ} (hR : 0<R) (F : Lp ℝ ∞ (cubeVolume R)) :
    ‖sourceVector hR F‖≤‖constantVector hR‖*‖F‖ := by
  rw [sourceVector_as_multiplier]
  exact (PhysicalFrequencyBounds.multiply_explicit_bound (source_memLp_reference hR F)
    ((reference_volume_equivalent hR).2.ae_le (LinftyRowOperator.ae_norm_bound F)) _).trans_eq
      (mul_comm _ _)

def sourceLinear {R : ℝ} (hR : 0<R) : Lp ℝ ∞ (cubeVolume R)→ₗ[ℝ]Space R where
  toFun := sourceVector hR
  map_add' := sourceVector_add hR
  map_smul' := sourceVector_smul hR

def sourceMap {R : ℝ} (hR : 0<R) : Lp ℝ ∞ (cubeVolume R)→L[ℝ]Space R :=
  (sourceLinear hR).mkContinuous ‖constantVector hR‖ (sourceVector_bound hR)

def functional {R : ℝ} (hR : 0<R) (F : Lp ℝ ∞ (cubeVolume R)) : Space R→L[ℝ]ℝ :=
  moment hR (source_memLp_reference hR F)

theorem functional_apply {R : ℝ} (hR : 0<R) (F : Lp ℝ ∞ (cubeVolume R)) (u : Space R) :
    functional hR F u=∫k,u k*F k∂cubeVolume R := moment_apply hR _ u

theorem functional_add {R : ℝ} (hR : 0<R) (F G : Lp ℝ ∞ (cubeVolume R)) :
    functional hR (F+G)=functional hR F+functional hR G := by
  ext u
  simp only [ContinuousLinearMap.add_apply,functional_apply]
  calc
    _=∫k,u k*F k+u k*G k∂cubeVolume R := by
      apply integral_congr_ae
      filter_upwards [Lp.coeFn_add F G] with k hk
      simp only [Pi.add_apply] at hk
      rw [hk,mul_add]
    _=_ := integral_add (weighted_moment_integrable hR (source_memLp_reference hR F) u)
      (weighted_moment_integrable hR (source_memLp_reference hR G) u)

theorem functional_smul {R : ℝ} (hR : 0<R) (a : ℝ) (F : Lp ℝ ∞ (cubeVolume R)) :
    functional hR (a • F)=a • functional hR F := by
  ext u
  simp only [ContinuousLinearMap.smul_apply,smul_eq_mul,functional_apply]
  calc
    _=∫k,a*(u k*F k)∂cubeVolume R := by
      apply integral_congr_ae
      filter_upwards [Lp.coeFn_smul a F] with k hk
      simp only [Pi.smul_apply,smul_eq_mul] at hk
      rw [hk]
      ring
    _=_ := integral_const_mul _ _

def functionalLinear {R : ℝ} (hR : 0<R) :
    Lp ℝ ∞ (cubeVolume R)→ₗ[ℝ](Space R→L[ℝ]ℝ) where
  toFun := functional hR
  map_add' := functional_add hR
  map_smul' := functional_smul hR

theorem functional_bound {R : ℝ} (hR : 0<R) (F : Lp ℝ ∞ (cubeVolume R)) :
    ‖functional hR F‖≤‖inverseVector hR‖*‖F‖ :=
  BoundedCellSource.source_norm_bound hR (source_memLp_reference hR F) (norm_nonneg F)
    ((reference_volume_equivalent hR).2.ae_le (LinftyRowOperator.ae_norm_bound F))

def functionalMap {R : ℝ} (hR : 0<R) :
    Lp ℝ ∞ (cubeVolume R)→L[ℝ](Space R→L[ℝ]ℝ) :=
  (functionalLinear hR).mkContinuous ‖inverseVector hR‖ (functional_bound hR)

end
end Resonance.BoundedSourceMaps
