import Resonance.ActualFourierExponential
import Resonance.L2BoundedExponential

/-! The original five-moment symbols, jointly acting on every square-
summable mode. All positive-time bounds and strong continuity are derived;
the only inputs are the original positive parameter and positive clock. -/
namespace Resonance.ActualCoefficientSemigroup
noncomputable section
open scoped NNReal
open Thermodynamics MatrixHilbertDictionary ActualUniformHilbertData ActualCompensatedDecay
open ActualFourierExponential HilbertExponentialFlow L2DiagonalOperator L2BoundedExponential
variable {I : Type*} {R : ℝ} (hR : 0<R) {θ : Parameter} (hθ : θ∈positiveDomain R)
variable {c : ℝ} (hc : 0<c) (r : I→ℝ) (hr : ∀i,0≤r i) (w : I→UnitDirection)

def coefficientSemigroup (t : ℝ≥0) : Space I H→L[ℂ]Space I H :=
  semigroup (fun i=>modeGenerator hR hθ (w i) c (r i)) (Real.sqrt_nonneg 3)
    (fun t i=>original_exponential_bound hR hθ (w i) hc (hr i) t.property) t

theorem coefficientSemigroup_apply (t : ℝ≥0) (v : Space I H) (i : I) :
    coefficientSemigroup hR hθ hc r hr w t v i=
      flow (modeGenerator hR hθ (w i) c (r i)) t (v i) := rfl

theorem coefficientSemigroup_zero : coefficientSemigroup hR hθ hc r hr w 0=1 :=
  semigroup_zero _ _ _

theorem coefficientSemigroup_add (s t : ℝ≥0) :
    coefficientSemigroup hR hθ hc r hr w (s+t)=
      coefficientSemigroup hR hθ hc r hr w s*coefficientSemigroup hR hθ hc r hr w t :=
  semigroup_add _ _ _ s t

theorem coefficientSemigroup_norm (t : ℝ≥0) :
    ‖coefficientSemigroup hR hθ hc r hr w t‖≤Real.sqrt 3 := semigroup_norm _ _ _ t

theorem coefficientSemigroup_strong_continuous (v : Space I H) :
    Continuous (fun t : ℝ≥0=>coefficientSemigroup hR hθ hc r hr w t v) :=
  semigroup_strong_continuous _ _ _ v

end
end Resonance.ActualCoefficientSemigroup
