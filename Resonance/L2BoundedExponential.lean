import Resonance.L2DiagonalContinuity
import Resonance.HilbertExponentialFlow

/-! One strongly continuous positive-time semigroup on the completed
common coefficient space. Its pointwise entries are the actual exponentials;
the uniform exponential bound is supplied by the preceding compensation
theorem when this constructor is used for the kinetic symbols. -/
open ContinuousLinearMap
open scoped NNReal
namespace Resonance.L2BoundedExponential
noncomputable section
open L2DiagonalOperator L2DiagonalContinuity HilbertExponentialFlow
variable {I E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

def semigroup (G : I→E→L[ℂ]E) {C : ℝ} (hC : 0≤C)
    (hG : ∀t : ℝ≥0,∀i,‖flow (G i) t‖≤C) (t : ℝ≥0) :
    Space I E→L[ℂ]Space I E := diagonal (fun i=>flow (G i) t) hC (hG t)

omit [CompleteSpace E] in
theorem semigroup_apply (G : I→E→L[ℂ]E) {C : ℝ} (hC : 0≤C)
    (hG : ∀t : ℝ≥0,∀i,‖flow (G i) t‖≤C) (t : ℝ≥0) (v : Space I E) (i : I) :
    semigroup G hC hG t v i=flow (G i) t (v i) := rfl

omit [CompleteSpace E] in
theorem semigroup_zero (G : I→E→L[ℂ]E) {C : ℝ} (hC : 0≤C)
    (hG : ∀t : ℝ≥0,∀i,‖flow (G i) t‖≤C) : semigroup G hC hG 0=1 := by
  ext v i
  simp only [semigroup_apply,NNReal.coe_zero,flow_zero,ContinuousLinearMap.one_apply]

theorem semigroup_add (G : I→E→L[ℂ]E) {C : ℝ} (hC : 0≤C)
    (hG : ∀t : ℝ≥0,∀i,‖flow (G i) t‖≤C) (s t : ℝ≥0) :
    semigroup G hC hG (s+t)=semigroup G hC hG s*semigroup G hC hG t := by
  ext v i
  simp only [semigroup_apply,NNReal.coe_add,flow_add,ContinuousLinearMap.mul_apply]

omit [CompleteSpace E] in
theorem semigroup_norm (G : I→E→L[ℂ]E) {C : ℝ} (hC : 0≤C)
    (hG : ∀t : ℝ≥0,∀i,‖flow (G i) t‖≤C) (t : ℝ≥0) : ‖semigroup G hC hG t‖≤C :=
  diagonal_norm _ hC (hG t)

theorem semigroup_strong_continuous (G : I→E→L[ℂ]E) {C : ℝ} (hC : 0≤C)
    (hG : ∀t : ℝ≥0,∀i,‖flow (G i) t‖≤C) (v : Space I E) :
    Continuous (fun t : ℝ≥0=>semigroup G hC hG t v) := by
  apply diagonal_strong_continuous (fun t : ℝ≥0=>fun i=>flow (G i) t) hC hG
  intro i x
  have hc : Continuous (fun s : ℝ=>flow (G i) s x) :=
    continuous_iff_continuousAt.mpr (fun s=>(flow_hasDerivAt (G i) x s).continuousAt)
  exact hc.comp NNReal.continuous_coe

end
end Resonance.L2BoundedExponential
