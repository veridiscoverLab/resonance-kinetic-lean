import Resonance.OppositeCornerBox
import Resonance.SmallBoxFrequency

/-! The original same-corner opposite-leg conditional mass is paid
by the original frequency with a quadratic corner-width factor. -/
open Real Set MeasureTheory
open scoped ENNReal
namespace Resonance.OppositeSameCornerMass
noncomputable section
open PlaneCoarea CollisionFiber CollisionFrequency CubeAxisCoordinates
open OppositeCornerBox SmallBoxFrequency
set_option maxHeartbeats 1200000

theorem normalized_output_upperCorner {L τ e : ℝ} (hL : 0<L) {d : Fin 3→ℝ}
    (hd0 : ∀i,0≤d i) (hde : ∀i,d i≤e) (heτ : e≤τ/2) :
    L•normalizedOutput d∈upperCorner (L/2) ((L*τ)/2) := by
  intro i
  change L/2-(L*τ)/2≤L*(1/2-d i) ∧ L*(1/2-d i)≤L/2
  constructor
  · nlinarith [hde i]
  · nlinarith [hd0 i]

theorem original_small_box_output {L τ : ℝ} (hτ : 0<τ) (d : Fin 3→ℝ) :
    L•normalizedOutput d-boxCenter (L/2) ((L*τ)/2)=
      (L*τ)•normalizedOutput (fun i=>d i/τ) := by
  ext i
  change L*(1/2-d i)-(L/2-(L*τ)/2)=(L*τ)*(1/2-d i/τ)
  field_simp
  ring

theorem original_same_corner_relative_mass {L : ℝ} (hL : 0<L) {d : Fin 3→ℝ} {e τ : ℝ}
    (hd0 : ∀i,0≤d i) (hde : ∀i,d i≤e) (hmax : ∃i,d i=e)
    (he : 0<e) (he1 : e≤(1:ℝ)/256) (hτ : 0<τ) (hτ1 : τ≤1) (heτ : e≤τ/2) :
    fiberMeasure (L/2) (L•normalizedOutput d)
      (oppositeCorner (L/2) ((L*τ)/2))≤
      ENNReal.ofReal (smallBoxConstant*τ^2*geometricFrequency (L/2) (L•normalizedOutput d)) := by
  have h := actual_opposite_corner_mass (by positivity : 0≤(L*τ)/2) (L•normalizedOutput d)
    (normalized_output_upperCorner hL hd0 hde heτ)
  rw [original_small_box_output hτ d] at h
  exact h.trans (ENNReal.ofReal_le_ofReal
    (actual_small_box_frequency hL hd0 hde hmax he he1 hτ hτ1 (by linarith)))

end
end Resonance.OppositeSameCornerMass
