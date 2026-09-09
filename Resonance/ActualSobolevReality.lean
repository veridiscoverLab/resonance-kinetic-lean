import Resonance.ActualSobolevSemigroup
import Resonance.ActualFourierReality
import Resonance.PhysicalFourierReality

/-! The genuine real subspace of the original H^s,M completion is
preserved. Whenever a Sobolev element is realized in physical L², this
condition is proved equivalent to real-valued physical components. -/
open MeasureTheory
open scoped NNReal
namespace Resonance.ActualSobolevReality
noncomputable section
open Thermodynamics MatrixHilbertDictionary ActualSobolevSpace ActualSobolevSemigroup
open PhysicalScalarFourier PhysicalVectorFourier ActualFourierReality
open ActualModeReconstruction SpatialTorusNormalization

def IsReal {R : ℝ} (hR : 0<R) {θ : Parameter} (hθ : θ∈positiveDomain R)
    (s : ℝ) (v : Sobolev s) : Prop :=
  ∀n:Frequency,coefficient hR hθ s v (-n)=conjugation (coefficient hR hθ s v n)

theorem evolution_preserves_real {R : ℝ} (hR : 0<R) {θ : Parameter}
    (hθ : θ∈positiveDomain R) {c : ℝ} (hc : 0<c) (s : ℝ) (t : ℝ≥0)
    (v : Sobolev s) (hv : IsReal hR hθ s v) :
    IsReal hR hθ s (evolution hR hθ hc s t v) := by
  intro n
  rw [evolution_original_mode,evolution_original_mode,hv n]
  have hn : (fun j=>((-n) j:ℝ))= -(fun j=>(n j:ℝ)) := by ext j; simp
  rw [hn]
  exact (physicalFlow_conjugate hR hθ c _ _ t.property).symm

theorem real_iff_physical_values {R : ℝ} (hR : 0<R) {θ : Parameter}
    (hθ : θ∈positiveDomain R) (s : ℝ) (v : Sobolev s) (f : Field)
    (hf : ∀n:Frequency,vectorFourier f n=coefficient hR hθ s v n) :
    IsReal hR hθ s v ↔ ∀j:Fin 5,∀ᵐx∂spatialHaar,star (f j x)=f j x := by
  constructor
  · intro hv j
    apply (PhysicalFourierReality.real_iff_fourier_symmetry (f j)).mpr
    intro n
    have hh := congrArg (fun w:H=>w j) (hv n)
    rw [←hf (-n),←hf n] at hh
    dsimp only at hh
    rw [conjugation_apply] at hh
    exact hh
  · intro hv n
    apply WithLp.ofLp_injective 2
    funext j
    have hh := (PhysicalFourierReality.real_iff_fourier_symmetry (f j)).mp (hv j) n
    have hneg := congrArg (fun w:H=>w j) (hf (-n))
    have hpos := congrArg (fun w:H=>w j) (hf n)
    change fourierIsometry (f j) (-n)=coefficient hR hθ s v (-n) j at hneg
    change fourierIsometry (f j) n=coefficient hR hθ s v n j at hpos
    change coefficient hR hθ s v (-n) j=star (coefficient hR hθ s v n j)
    rw [←hneg,←hpos]
    exact hh

end
end Resonance.ActualSobolevReality
