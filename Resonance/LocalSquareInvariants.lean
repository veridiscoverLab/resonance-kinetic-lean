import Resonance.ComplexFiveInvariants

/-! The paper's local L² hypothesis is discharged on each compact subset
of the original open cube, rather than replaced by a smoothness hypothesis. -/
open Set MeasureTheory
open scoped ENNReal

namespace Resonance.LocalSquareInvariants
noncomputable section
open ResonantMeasure ContinuousCollisionInvariants QuadraticPointwiseClosure FiveInvariantFinal

def LocalSquareIntegrableOn {F : Type*} [NormedAddCommGroup F] (f : E → F) (U : Set E) : Prop :=
  ∀ K : Set E, K ⊆ U → IsCompact K → MemLp f 2 ((volume : Measure E).restrict K)

theorem localSquare_locallyIntegrable {F : Type*} [NormedAddCommGroup F]
    {f : E → F} {U : Set E} (hU : IsOpen U) (hf : LocalSquareIntegrableOn f U) :
    LocallyIntegrableOn f U := by
  rw [locallyIntegrableOn_iff hU.isLocallyClosed]
  intro K hKU hK
  letI : IsFiniteMeasure ((volume : Measure E).restrict K) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact hK.measure_lt_top⟩
  exact (hf K hKU hK).integrable (by norm_num)

theorem original_real_L2local_classification {R : ℝ} (hR : 0<R) {f : E → ℝ}
    (hfl : LocalSquareIntegrableOn f (openCube R)) (hf : invariant R f) :
    ∃! b : Coefficients, f =ᵐ[(volume : Measure E).restrict (cube R)] evaluate b :=
  original_cube_invariant_unique hR (localSquare_locallyIntegrable (openCube_isOpen R) hfl) hf

theorem original_complex_L2local_classification {R : ℝ} (hR : 0<R) {f : E → ℂ}
    (hfl : LocalSquareIntegrableOn f (openCube R)) (hf : ComplexFiveInvariants.invariant R f) :
    ∃! b : ComplexFiveInvariants.ComplexCoefficients,
      f =ᵐ[(volume : Measure E).restrict (cube R)] ComplexFiveInvariants.evaluateComplex b :=
  ComplexFiveInvariants.original_complex_invariant_unique hR
    (localSquare_locallyIntegrable (openCube_isOpen R) hfl) hf

end
end Resonance.LocalSquareInvariants
