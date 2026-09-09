import Resonance.NormalizedCornerRoles
import Resonance.SignedCornerEvents
import Resonance.CornerInverseFrequency

/-! Original conditional role mass at every output in all eight
corner layers. Zero-frequency corner outputs are handled directly. -/
open Real Set MeasureTheory
open scoped ENNReal
namespace Resonance.OriginalNearCornerRoles
noncomputable section
open ResonantMeasure CollisionFiber CollisionFrequency CubeFrequencyReflection
open CornerFrequencyBounds CornerInverseFrequency CornerRoleGeometry
open NormalizedCornerRoles SignedCornerEvents
set_option maxHeartbeats 1400000

theorem original_near_opposite_mass {R : ℝ} (hR : 0 < R) (k : E) (hk : k∈cube R)
    {t : ℝ} (ht : 0 < t) (ht1 : t ≤ (1:ℝ)/4096) (hkt : cornerDepth R k ≤ t) :
    fiberMeasure R k (legLayer R (2*R*t) 1) ≤
      ENNReal.ofReal (oppositeConstant*t*geometricFrequency R k) := by
  by_cases he : 0 < cornerDepth R k
  · have hm := original_normalized_opposite_corner (by positivity : 0 < 2*R)
      he ht ht1 hkt (fun j => (cornerCoordinates_bounds hR k hk j).1)
      (le_maxDeficit (cornerCoordinates R k)) (maxDeficit_attained (cornerCoordinates R k))
    have hrad : (2*R)/2=R := by ring
    rw [hrad,←reflected_output_eq_scaled hR k,original_frequency_reflection hR.le k hk] at hm
    rw [original_layer_reflection hR.le (2*R*t) k hk 1]
    exact hm
  · rw [fiberMeasure_corner_zero (corner_of_nonpositive_depth hR hk (le_of_not_gt he))]
    simp

theorem original_near_adjacent_wrong_mass {R : ℝ} (hR : 0 < R) (k : E) (hk : k∈cube R)
    {t : ℝ} (ht : 0 < t) (ht1 : t ≤ (1:ℝ)/4096) (hkt : cornerDepth R k ≤ t)
    (l : Fin 4) (hl : l=2 ∨ l=3) :
    fiberMeasure R k (wrongSignedLayer R (2*R*t) k l) ≤
      ENNReal.ofReal (adjacentConstant*t*geometricFrequency R k) := by
  by_cases he : 0 < cornerDepth R k
  · have hm := original_normalized_wrong_corner (by positivity : 0 < 2*R)
      he ht ht1 hkt (fun j => (cornerCoordinates_bounds hR k hk j).1)
      (le_maxDeficit (cornerCoordinates R k)) (maxDeficit_attained (cornerCoordinates R k)) l hl
    have hrad : (2*R)/2=R := by ring
    rw [hrad,←reflected_output_eq_scaled hR k,original_frequency_reflection hR.le k hk] at hm
    rw [original_wrong_reflection hR.le (2*R*t) k hk l]
    exact hm
  · rw [fiberMeasure_corner_zero (corner_of_nonpositive_depth hR hk (le_of_not_gt he))]
    simp

end
end Resonance.OriginalNearCornerRoles
