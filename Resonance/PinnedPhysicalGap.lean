import Resonance.PinnedPhysicalForm
import Resonance.HilbertPullbackDistance

/-! The physical relative-variable gap in the original unweighted L²
norm. It is derived from the full coarea gap and the actual inverse
multiplier bound, not from an isometric change of variables. -/
open Set MeasureTheory
namespace Resonance.PinnedPhysicalGap
noncomputable section
open PinnedPeriodicity PinnedEndToEnd PinnedClassificationFinal PinnedMaximalDifference
open PinnedPhysicalMultiplier PinnedPhysicalForm
local notation "Circle" => PinnedPeriodicity.Circle
local instance periodPositive : Fact (0 < period) := ⟨period_pos⟩

def physicalNull {d : ℝ} (hd0 : 0 < d) (hdU : d < 1/2)
    (N : C(Circle,ℝ)) (hN : ∀ x, 0 < N x) : Submodule ℂ Source :=
  (PinnedGap.nullSpace hd0 hdU (physicalWeight d N)).comap
    (physicalEquivalence N hN).toLinearMap

theorem physicalNull_isClosed {d : ℝ} (hd0 : 0 < d) (hdU : d < 1/2)
    (N : C(Circle,ℝ)) (hN : ∀ x, 0 < N x) :
    IsClosed (physicalNull hd0 hdU N hN : Set Source) :=
  HilbertPullbackDistance.comap_isClosed _ (PinnedGap.nullSpace_isClosed hd0 hdU _) _

instance physicalNull_complete {d : ℝ} (hd0 : 0 < d) (hdU : d < 1/2)
    (N : C(Circle,ℝ)) (hN : ∀ x, 0 < N x) : CompleteSpace (physicalNull hd0 hdU N hN) :=
  (physicalNull_isClosed hd0 hdU N hN).isComplete.completeSpace_coe

theorem physicalNull_iff {d : ℝ} (hd0 : 0 < d) (hdU : d < 1/2)
    (N : C(Circle,ℝ)) (hN : ∀ x, 0 < N x) (u : Source) :
    u ∈ physicalNull hd0 hdU N hN ↔ (u,0) ∈ (physicalDifference hd0 hdU N hN).graph := by
  rw [physicalDifference,ClosedPullback.graph_iff,maximalDifference_graph]
  rfl

theorem physicalNull_classification {d : ℝ} (hd0 : 0 < d) (hdU : d < 1/2)
    (N : C(Circle,ℝ)) (hN : ∀ x, 0 < N x) (u : Source) :
    u ∈ physicalNull hd0 hdU N hN ↔ ExistsUnique (fun AB : ℂ × ℂ =>
      (u : Circle → ℂ) =ᵐ[circleHaar]
        (fun x => (N x : ℂ)*(AB.1+AB.2*(circleDispersion d x : ℂ)))) := by
  rw [physicalNull_iff,physical_kernel_classification]

theorem physical_distance_bound {d : ℝ} (hd0 : 0 < d) (hdU : d < 1/2)
    (N : C(Circle,ℝ)) (hN : ∀ x, 0 < N x) (u : Source) :
    ‖u-(physicalNull hd0 hdU N hN).starProjection u‖ ≤ ‖N‖*
      ‖physicalEquivalence N hN u-(PinnedGap.nullSpace hd0 hdU (physicalWeight d N)).starProjection
        (physicalEquivalence N hN u)‖ := by
  letI : CompleteSpace ((PinnedGap.nullSpace hd0 hdU (physicalWeight d N)).comap
      (physicalEquivalence N hN).toLinearMap) := physicalNull_complete hd0 hdU N hN
  exact HilbertPullbackDistance.pullback_distance_bound _ _ _ (physical_inverse_bound N hN) u

theorem physical_form_spectral_gap {d : ℝ} (hd0 : 0 < d) (hdU : d < 1/2)
    (N : C(Circle,ℝ)) (hN : ∀ x, 0 < N x) :
    ∃ lam : ℝ, 0 < lam ∧ ∀ (γ : ℝ), 0 ≤ γ → ∀ u : PhysicalDomain hd0 hdU N hN,
      (γ/4)*lam*‖(u : Source)-(physicalNull hd0 hdU N hN).starProjection u‖^2
        ≤ (physicalForm hd0 hdU N hN γ u u).re := by
  obtain ⟨lam,hlam,hgap⟩ := PinnedOperator.form_spectral_gap hd0 hdU
    (physicalWeight_continuous hd0 hdU N) (physicalWeight_positive hd0 hdU N hN)
  let C := ‖N‖+1
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨lam/C^2,div_pos hlam (sq_pos_of_pos hC),?_⟩
  intro γ hγ u
  let T := maximalDifference hd0 hdU (physicalWeight d N)
  let U := physicalEquivalence N hN
  let v := ClosedPullback.domainMap T U u
  have hg := hgap γ hγ v
  have hd := physical_distance_bound hd0 hdU N hN u
  let a := ‖(u : Source)-(physicalNull hd0 hdU N hN).starProjection u‖
  let b := ‖U (u : Source)-(PinnedGap.nullSpace hd0 hdU (physicalWeight d N)).starProjection
    (U (u : Source))‖
  have hab : a ≤ C*b := le_trans hd (mul_le_mul_of_nonneg_right (by dsimp [C]; linarith) (norm_nonneg _))
  have hs : a^2 ≤ C^2*b^2 := by
    have h := mul_self_le_mul_self (norm_nonneg _) hab
    nlinarith
  have hr : (lam/C^2)*a^2 ≤ lam*b^2 := by
    have hc2 := sq_pos_of_pos hC
    calc
      _ = (lam*a^2)/C^2 := by ring
      _ ≤ lam*b^2 := (div_le_iff₀ hc2).mpr (by
        convert mul_le_mul_of_nonneg_left hs hlam.le using 1; ring)
  have hscale := mul_le_mul_of_nonneg_left hr (show 0 ≤ γ/4 by positivity)
  change (γ/4)*lam*b^2 ≤ (physicalForm hd0 hdU N hN γ u u).re at hg
  change (γ/4)*(lam/C^2)*a^2 ≤ _
  exact le_trans (by simpa only [mul_assoc] using hscale) hg

end
end Resonance.PinnedPhysicalGap
