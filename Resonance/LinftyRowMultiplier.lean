import Resonance.LinftyRowOperator
import Resonance.ContinuousRowMultiplier

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace Resonance.LinftyRowMultiplier
noncomputable section
variable {X Y : Type*} [TopologicalSpace X] [CompactSpace X]
  [MeasurableSpace Y] {μ : Measure Y}

theorem exists_compact_mul_operator (K : X → Y → ℝ) (hi : ∀ x, Integrable (K x) μ)
    (hc : ∀ x, Tendsto (fun a => ∫ y, ‖K a y-K x y‖ ∂μ) (𝓝 x) (𝓝 0))
    (b : Y → ℝ) (hbm : AEStronglyMeasurable b μ) {B : ℝ} (hB : 0 ≤ B)
    (hb : ∀ᵐ y ∂μ, ‖b y‖ ≤ B) (a : C(X,ℝ)) :
    ∃ T : Lp ℝ ∞ μ →L[ℝ] C(X,ℝ), IsCompactOperator T ∧
      ∀ f x, T f x = a x*(∫ y, (K x y*b y)*f y ∂μ) := by
  obtain ⟨T,hT,hread⟩ := LinftyRowOperator.exists_compact_operator
    (fun x y => K x y*b y) (ContinuousRowMultiplier.mul_rows_integrable K hi b hbm hb)
    (ContinuousRowMultiplier.mul_rows_L1_continuous K hi hc b hbm hB hb)
  let M := ContinuousLinearMap.mul ℝ C(X,ℝ) a
  refine ⟨M.comp T,hT.clm_comp M,?_⟩
  intro f x
  change a x*T f x=_
  rw [hread]

end
end Resonance.LinftyRowMultiplier
