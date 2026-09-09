import Resonance.PinnedPhysicalForm
import Resonance.ClosedSquareKernel

/-! The physical g-variable realization represents the complete form
on its maximal domain, with its exact two-dimensional physical kernel. -/
open Set MeasureTheory LinearPMap
open scoped ComplexConjugate
namespace Resonance.PinnedPhysicalRealization
noncomputable section
open PinnedPeriodicity PinnedEndToEnd PinnedClassificationFinal PinnedMaximalDifference
open PinnedPhysicalMultiplier PinnedPhysicalForm PinnedScaledDifference
local notation "Circle" => PinnedPeriodicity.Circle
local instance periodPositive : Fact (0 < period) := ⟨period_pos⟩

theorem physical_scaled_inner {d : ℝ} (hd0 : 0 < d) (hdU : d < 1/2)
    (N : C(Circle,ℝ)) (hN : ∀ x, 0 < N x) {γ : ℝ} (hγ : 0 ≤ γ)
    (u v : PhysicalDomain hd0 hdU N hN) :
    inner ℂ (ClosedPullback.pullback (scaledDifference hd0 hdU (physicalWeight d N) γ)
      (physicalEquivalence N hN) u)
      (ClosedPullback.pullback (scaledDifference hd0 hdU (physicalWeight d N) γ)
        (physicalEquivalence N hN) v) = physicalForm hd0 hdU N hN γ v u :=
  scaled_inner_eq_form hd0 hdU (physicalWeight d N) hγ _ _

theorem physicalOperator_graph_iff {d : ℝ} (hd0 : 0 < d) (hdU : d < 1/2)
    (N : C(Circle,ℝ)) (hN : ∀ x, 0 < N x) {γ : ℝ} (hγ : 0 ≤ γ) (x z : Source) :
    (x,z) ∈ (physicalOperator hd0 hdU N hN γ).graph ↔
      ∃ hx : x∈PhysicalDomain hd0 hdU N hN, ∀ y : PhysicalDomain hd0 hdU N hN,
        inner ℂ z (y : Source) = physicalForm hd0 hdU N hN γ y ⟨x,hx⟩ := by
  rw [physicalOperator,ClosedOperatorRepresentation.square_graph_iff _
    (ClosedPullback.pullback_dense _
      (scaledDifference_dense_domain hd0 hdU (physicalWeight_continuous hd0 hdU N) γ) _)]
  simp only [physical_scaled_inner hd0 hdU N hN hγ]
  rfl

theorem physicalOperator_zero_graph_iff {d : ℝ} (hd0 : 0 < d) (hdU : d < 1/2)
    (N : C(Circle,ℝ)) (hN : ∀ x, 0 < N x) {γ : ℝ} (hγ : 0 < γ) (x : Source) :
    (x,0) ∈ (physicalOperator hd0 hdU N hN γ).graph ↔
      (x,0) ∈ (physicalDifference hd0 hdU N hN).graph := by
  rw [physicalOperator,ClosedSquareKernel.square_zero_graph_iff _
    (ClosedPullback.pullback_dense _
      (scaledDifference_dense_domain hd0 hdU (physicalWeight_continuous hd0 hdU N) γ) _)]
  rw [ClosedPullback.graph_iff,physicalDifference,ClosedPullback.graph_iff]
  have he := scaledDifference_graph hd0 hdU (physicalWeight d N) hγ
  change (physicalEquivalence N hN x,0) ∈
    ((scaledDifference hd0 hdU (physicalWeight d N) γ).graph : Set (Source × Target d (physicalWeight d N))) ↔ _
  rw [he]
  simp only [mem_preimage,smul_zero]
  rfl

theorem physicalOperator_kernel_classification {d : ℝ} (hd0 : 0 < d) (hdU : d < 1/2)
    (N : C(Circle,ℝ)) (hN : ∀ x, 0 < N x) {γ : ℝ} (hγ : 0 < γ) (u : Source) :
    (u,0) ∈ (physicalOperator hd0 hdU N hN γ).graph ↔ ExistsUnique (fun AB : ℂ × ℂ =>
      (u : Circle → ℂ) =ᵐ[circleHaar]
        (fun x => (N x : ℂ)*(AB.1+AB.2*(circleDispersion d x : ℂ)))) := by
  rw [physicalOperator_zero_graph_iff hd0 hdU N hN hγ,physical_kernel_classification]

theorem physicalOperator_nonnegative {d : ℝ} (hd0 : 0 < d) (hdU : d < 1/2)
    (N : C(Circle,ℝ)) (hN : ∀ x, 0 < N x) (γ : ℝ)
    (u : (physicalOperator hd0 hdU N hN γ).domain) :
    0 ≤ (inner ℂ (physicalOperator hd0 hdU N hN γ u) (u : Source)).re :=
  ClosedOperatorRepresentation.square_nonnegative _
    (ClosedPullback.pullback_dense _
      (scaledDifference_dense_domain hd0 hdU (physicalWeight_continuous hd0 hdU N) γ) _) u

theorem physicalOperator_unique {d : ℝ} (hd0 : 0 < d) (hdU : d < 1/2)
    (N : C(Circle,ℝ)) (hN : ∀ x, 0 < N x) {γ : ℝ} (hγ : 0 ≤ γ)
    (L : Source →ₗ.[ℂ] Source)
    (hL : ∀ x z : Source, (x,z) ∈ L.graph ↔
      ∃ hx : x∈PhysicalDomain hd0 hdU N hN, ∀ y : PhysicalDomain hd0 hdU N hN,
        inner ℂ z (y : Source) = physicalForm hd0 hdU N hN γ y ⟨x,hx⟩) :
    L = physicalOperator hd0 hdU N hN γ := by
  apply LinearPMap.eq_of_eq_graph
  apply SetLike.coe_injective
  apply Set.ext
  rintro ⟨x,z⟩
  exact (hL x z).trans (physicalOperator_graph_iff hd0 hdU N hN hγ x z).symm

end
end Resonance.PinnedPhysicalRealization
