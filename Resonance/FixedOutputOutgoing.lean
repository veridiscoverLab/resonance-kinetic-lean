import Resonance.SignedFiberReadout
import Resonance.CubeContinuousEssentialNorm
import Resonance.MarkedCoordinateSymmetry

/-! The original outgoing-leg symmetry holds at every fixed output
for continuous readouts, including all boundary and corner outputs. -/
open Real Set MeasureTheory
open scoped ENNReal
namespace Resonance.FixedOutputOutgoing
noncomputable section
open ResonantMeasure FiberContinuity SignedFiberReadout CubeContinuousEssentialNorm
open MarkedCoordinateSymmetry
set_option maxHeartbeats 1200000

theorem swapOutgoingK_continuous : Continuous swapOutgoingK := by
  apply continuous_pi
  intro i
  fin_cases i
  · exact continuous_apply 0
  · exact continuous_apply 1
  · exact continuous_apply 3
  · exact continuous_apply 2

theorem original_continuous_outgoing {R : ℝ} (hR : 0<R) {Φ : FourMomenta→ℝ}
    (hΦ : Continuous Φ) (k : E) (hk : k∈cube R) :
    fiberReadout R (Φ∘swapOutgoingK) k=fiberReadout R Φ k := by
  obtain ⟨B,hB,hbound⟩ := PolarCoordinates.continuous_four_flags_bound hR.le Φ hΦ
  have hae := ae_restrict_of_ae (s:=cube R) (original_outgoing_fiber_ae hR.le hB Φ hΦ.measurable hbound)
  have hc1 := fiberReadout_continuousOn hR.le (Φ∘swapOutgoingK) (hΦ.comp swapOutgoingK_continuous)
  have hc2 := fiberReadout_continuousOn hR.le Φ hΦ
  exact (Measure.eqOn_of_ae_eq (μ:=(volume:Measure E)) hae hc1 hc2
    (cube_subset_closure_interior hR)) hk

theorem coordinateMark_outgoing (L : ℝ) (i : Fin 3) (w : ℝ×ℝ→ℝ) :
    (coordinateMark L i w)∘swapOutgoingK=coordinateMark L i (fun p=>w p.swap) := by
  ext q
  simp [coordinateMark,swapOutgoingK]

theorem actual_coordinate_mark_swap {R : ℝ} (hR : 0<R) (L : ℝ) (i : Fin 3)
    {w : ℝ×ℝ→ℝ} (hw : Continuous w) (k : E) (hk : k∈cube R) :
    fiberReadout R (coordinateMark L i (fun p=>w p.swap)) k=
      fiberReadout R (coordinateMark L i w) k := by
  rw [←coordinateMark_outgoing]
  exact original_continuous_outgoing hR (coordinateMark_continuous L i hw) k hk

end
end Resonance.FixedOutputOutgoing
