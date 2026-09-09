import Resonance.PinnedPhysicalGap
import Resonance.PinnedUniformFormGap

/-! Uniform physical gaps from actual common weight and multiplier
bounds. The fixed dispersion-dependent gap is derived from coarea. -/
open Set MeasureTheory
namespace Resonance.PinnedPhysicalUniform
noncomputable section
open PinnedPeriodicity PinnedEndToEnd PinnedClassificationFinal PinnedMaximalDifference
open PinnedPhysicalMultiplier PinnedPhysicalForm PinnedPhysicalGap
local notation "Circle" => PinnedPeriodicity.Circle
local instance periodPositive : Fact (0 < period) := ⟨period_pos⟩

theorem physical_uniform_bound {d : ℝ} (hd0 : 0 < d) (hdU : d < 1/2)
    {b C : ℝ} (hb : 0 < b) (hC : 0 < C) :
    ∃ lam : ℝ, 0 < lam ∧ ∀ (N : C(Circle,ℝ)) (hN : ∀ x, 0 < N x),
      (∀ k, b ≤ physicalWeight d N k) → ‖N‖ ≤ C →
      ∀ (γ : ℝ), 0 ≤ γ → ∀ u : PhysicalDomain hd0 hdU N hN,
        (γ/4)*lam*‖(u : Source)-(physicalNull hd0 hdU N hN).starProjection u‖^2
          ≤ (physicalForm hd0 hdU N hN γ u u).re := by
  obtain ⟨lam,hlam,hgap⟩ := PinnedUniformFormGap.uniform_form_lower_bound hd0 hdU
  refine ⟨(b*lam)/C^2,div_pos (mul_pos hb hlam) (sq_pos_of_pos hC),?_⟩
  intro N hN hweight hnorm γ hγ u
  let T := maximalDifference hd0 hdU (physicalWeight d N)
  let U := physicalEquivalence N hN
  let v := ClosedPullback.domainMap T U u
  have hg := hgap (physicalWeight d N) (physicalWeight_continuous hd0 hdU N) b hb hweight γ hγ v
  have hd := physical_distance_bound hd0 hdU N hN u
  let x := ‖(u : Source)-(physicalNull hd0 hdU N hN).starProjection u‖
  let y := ‖U (u : Source)-(PinnedGap.nullSpace hd0 hdU (physicalWeight d N)).starProjection
    (U (u : Source))‖
  have hxy : x ≤ C*y := le_trans hd (mul_le_mul_of_nonneg_right hnorm (norm_nonneg _))
  have hs : x^2 ≤ C^2*y^2 := by
    have h := mul_self_le_mul_self (norm_nonneg _) hxy
    nlinarith
  have hr : ((b*lam)/C^2)*x^2 ≤ (b*lam)*y^2 := by
    calc
      _ = ((b*lam)*x^2)/C^2 := by ring
      _ ≤ (b*lam)*y^2 := (div_le_iff₀ (sq_pos_of_pos hC)).mpr (by
        convert mul_le_mul_of_nonneg_left hs (mul_pos hb hlam).le using 1; ring)
  have hscale := mul_le_mul_of_nonneg_left hr (show 0 ≤ γ/4 by positivity)
  change (γ/4)*(b*lam)*y^2 ≤ (physicalForm hd0 hdU N hN γ u u).re at hg
  change (γ/4)*((b*lam)/C^2)*x^2 ≤ _
  exact le_trans (by simpa only [mul_assoc] using hscale) hg

end
end Resonance.PinnedPhysicalUniform
