import Resonance.PinnedRJProfile
import Resonance.QuartetPhysicalLinearization

/-! The first variation of the original pinned four-wave collision
expression on the same actual coarea, with the physical sign and weight.
Differentiation is pointwise before integration; no unsupported exchange
of an infinite singular integral and a derivative is asserted. -/
open Set MeasureTheory
namespace Resonance.PinnedPhysicalLinearization
noncomputable section
open PinnedPeriodicity PinnedEndToEnd PinnedClassificationFinal PinnedMeasureNormalization
open PinnedMaximalDifference PinnedPhysicalMultiplier PinnedRJProfile
open QuartetPhysicalLinearization
local notation "Circle" => PinnedPeriodicity.Circle
local instance periodPositive : Fact (0 < period) := ⟨period_pos⟩

theorem actual_inverse_equilibrium {d : ℝ} (hd0 : 0 < d) (hdU : d < 1/2)
    (p : positiveDomain d) : ∀ᵐ k ∂euclideanCircleRegularCoarea d,
      delta (fun i => (profile hd0 hdU p (fullLegs k i))⁻¹)=0 := by
  have hi := affine_representative_euclidean_invariant hd0 hdU (p.val.1 : ℂ) (p.val.2 : ℂ)
  filter_upwards [hi] with k hk
  have hz := (difference_zero_iff _ k).mpr hk
  apply Complex.ofReal_injective
  simpa only [delta,profile_inverse,fullLegs,difference,Complex.ofReal_add,
    Complex.ofReal_sub,Complex.ofReal_mul,Complex.ofReal_zero] using hz

def collisionExpression (d γ : ℝ) (W : Circle → ℝ) (k : CircleMomenta) : ℝ :=
  (γ/(∏ i,circleDispersion d (fullLegs k i)))*(∏ i,W (fullLegs k i))*
    delta (fun i => (W (fullLegs k i))⁻¹)

theorem original_pointwise_linearization {d : ℝ} (hd0 : 0 < d) (hdU : d < 1/2)
    (p : positiveDomain d) (φ : Circle → ℝ) (γ : ℝ) :
    ∀ᵐ k ∂euclideanCircleRegularCoarea d,
      HasDerivAt (fun t => collisionExpression d γ
        (fun x => profile hd0 hdU p x+t*((profile hd0 hdU p x)^2*φ x)) k)
        (-γ*physicalWeight d (profile hd0 hdU p) (fullLegs k)*delta (fun i => φ (fullLegs k i))) 0 := by
  filter_upwards [actual_inverse_equilibrium hd0 hdU p] with k hk
  have h := weighted_complete_linearization
    (fun i => profile hd0 hdU p (fullLegs k i)) (fun i => φ (fullLegs k i))
    (fun i => (profile_positive hd0 hdU p (fullLegs k i)).ne') hk
    (γ/(∏ i,circleDispersion d (fullLegs k i)))
  convert h using 1
  · funext t
    simp only [collisionExpression,collisionFactor,perturbation]
    ring
  · rw [physicalWeight_formula]
    ring

end
end Resonance.PinnedPhysicalLinearization
