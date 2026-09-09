import Resonance.CornerRoleGeometry

/-! Original conditional role estimates near the positive corner,
for the whole eight-corner input layer. -/
open Real Set MeasureTheory
open scoped ENNReal
namespace Resonance.NormalizedCornerRoles
noncomputable section
open ResonantMeasure CollisionFiber CollisionFrequency CubeAxisCoordinates
open MarkedRelativeMass SmallBoxFrequency OppositeSameCornerMass
open NormalizedCornerStrips CornerRoleGeometry
set_option maxHeartbeats 1200000

def adjacentConstant : ℝ := 18*relativeConstant
def oppositeConstant : ℝ := 4*smallBoxConstant+456*relativeConstant

theorem adjacentConstant_nonneg : 0 ≤ adjacentConstant := by
  unfold adjacentConstant
  positivity [relativeConstant_nonneg]

theorem oppositeConstant_nonneg : 0 ≤ oppositeConstant := by
  unfold oppositeConstant
  positivity [relativeConstant_nonneg,smallBoxConstant_nonneg]

theorem three_ofReal (x : ℝ) : 3*ENNReal.ofReal x=ENNReal.ofReal (3*x) := by
  rw [show (3:ℝ≥0∞)=ENNReal.ofReal (3:ℝ) by norm_num,ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 3)]

theorem original_normalized_wrong_corner {L : ℝ} (hL : 0 < L) {d : Fin 3→ℝ}
    {e t : ℝ} (he : 0 < e) (ht : 0 < t) (ht1 : t ≤ (1:ℝ)/4096) (het : e ≤ t)
    (hd0 : ∀j,0 ≤ d j) (hde : ∀j,d j ≤ e) (hmax : ∃j,d j=e)
    (l : Fin 4) (hl : l=2 ∨ l=3) :
    fiberMeasure (L/2) (L•normalizedOutput d) (wrongUpperLayer (L/2) (L*t) l) ≤
      ENNReal.ofReal (adjacentConstant*t*geometricFrequency (L/2) (L•normalizedOutput d)) := by
  have h := (measure_mono (wrongUpperLayer_subset (L/2) (L*t) l)).trans
    (finite_axis_mass_bound (fiberMeasure (L/2) (L•normalizedOutput d)) (L/2) (L*t) l _
      (fun i => original_adjacent_lowerFace hL i he ht ht1 het hd0 hde hmax l hl))
  rw [three_ofReal] at h
  exact h.trans_eq (by congr 1; unfold adjacentConstant; ring)

theorem original_normalized_opposite_corner {L : ℝ} (hL : 0 < L) {d : Fin 3→ℝ}
    {e t : ℝ} (he : 0 < e) (ht : 0 < t) (ht1 : t ≤ (1:ℝ)/4096) (het : e ≤ t)
    (hd0 : ∀j,0 ≤ d j) (hde : ∀j,d j ≤ e) (hmax : ∃j,d j=e) :
    fiberMeasure (L/2) (L•normalizedOutput d) (legLayer (L/2) (L*t) 1) ≤
      ENNReal.ofReal (oppositeConstant*t*geometricFrequency (L/2) (L•normalizedOutput d)) := by
  have hs := original_same_corner_relative_mass hL hd0 hde hmax he (by linarith)
    (by positivity : 0 < 2*t) (by linarith : 2*t ≤ 1) (by linarith : e ≤ (2*t)/2)
  have heq : L*(2*t)/2=L*t := by ring
  rw [heq] at hs
  have hf := finite_axis_mass_bound (fiberMeasure (L/2) (L•normalizedOutput d)) (L/2) (L*t) 1 _
    (fun i => original_opposite_lowerFace hL i he ht ht1 het hd0 hde hmax)
  rw [three_ofReal] at hf
  have h := ((measure_mono (oppositeLayer_subset (L/2) (L*t))).trans (measure_union_le _ _)).trans
    (add_le_add hs hf)
  have hsmall := smallBoxConstant_nonneg
  have hrel := relativeConstant_nonneg
  have hM := geometricFrequency_nonnegative (L/2) (L•normalizedOutput d)
  rw [←ENNReal.ofReal_add (by positivity) (by positivity)] at h
  apply h.trans (ENNReal.ofReal_le_ofReal _)
  have ht2 : t^2 ≤ t := by nlinarith
  have hc : smallBoxConstant*(2*t)^2+3*((152*relativeConstant)*t) ≤ oppositeConstant*t := by
    unfold oppositeConstant
    nlinarith [mul_le_mul_of_nonneg_left ht2 hsmall]
  exact (show smallBoxConstant*(2*t)^2*geometricFrequency (L/2) (L•normalizedOutput d)+
      3*((152*relativeConstant)*t*geometricFrequency (L/2) (L•normalizedOutput d)) =
      (smallBoxConstant*(2*t)^2+3*((152*relativeConstant)*t))*
        geometricFrequency (L/2) (L•normalizedOutput d) by ring).le.trans
    (mul_le_mul_of_nonneg_right hc hM)

end
end Resonance.NormalizedCornerRoles
