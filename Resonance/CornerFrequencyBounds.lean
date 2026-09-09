import Resonance.CornerZeroBounds
import Resonance.CubeFrequencyReflection

/-! The sharp logarithmic scale for the original complete cube fiber.
The dimensionless depth is the largest distance to a closest coordinate
face, divided by the side length; hence all eight corners are included. -/
open Real Set MeasureTheory
open scoped ENNReal Topology
namespace Resonance.CornerFrequencyBounds
noncomputable section
set_option maxHeartbeats 600000
open Resonance.PlaneCoarea Resonance.CornerConvolution Resonance.CornerZeroBounds
open Resonance.CubeFrequencyReflection Resonance.CollisionFrequency

def maxDeficit (d:Fin 3→ℝ) : ℝ := max (d 0) (max (d 1) (d 2))
def cornerDepth (R:ℝ) (k:E) : ℝ := maxDeficit (cornerCoordinates R k)

theorem le_maxDeficit (d:Fin 3→ℝ) (i:Fin 3) : d i≤ maxDeficit d := by
  fin_cases i
  · exact le_max_left _ _
  · exact (le_max_left _ _).trans (le_max_right _ _)
  · exact (le_max_right _ _).trans (le_max_right _ _)

theorem maxDeficit_attained (d:Fin 3→ℝ) : ∃i,d i=maxDeficit d := by
  unfold maxDeficit
  rcases le_total (d 0) (max (d 1) (d 2)) with h|h
  · rw [max_eq_right h]
    rcases le_total (d 1) (d 2) with hh|hh
    · exact ⟨2,(max_eq_right hh).symm⟩
    · exact ⟨1,(max_eq_left hh).symm⟩
  · exact ⟨0,(max_eq_left h).symm⟩

theorem cornerDepth_nonnegative {R:ℝ} (hR:0<R) {k:E}
    (hk:k∈ResonantMeasure.cube R) : 0≤cornerDepth R k :=
  (cornerCoordinates_bounds hR k hk 0).1.trans (le_maxDeficit _ 0)

theorem cornerDepth_le_half {R:ℝ} (hR:0<R) {k:E}
    (hk:k∈ResonantMeasure.cube R) : cornerDepth R k≤1/2 := by
  unfold cornerDepth maxDeficit
  exact max_le (cornerCoordinates_bounds hR k hk 0).2
    (max_le (cornerCoordinates_bounds hR k hk 1).2 (cornerCoordinates_bounds hR k hk 2).2)

theorem geometricFrequency_eq_convolution_real {R:ℝ} (hR:0<R) {k:E}
    (hk:k∈ResonantMeasure.cube R) :
    geometricFrequency R k=((2*R)^4/2)*(sumDensity (cornerCoordinates R k) 0).toReal := by
  have he := congrArg ENNReal.toReal (full_cube_frequency_eq_convolution hR k hk)
  simpa only [ENNReal.toReal_mul,ENNReal.toReal_ofReal (geometricFrequency_nonnegative R k),
    ENNReal.toReal_ofReal (show 0≤(2*R)^4/2 by positivity)] using he

def geometricLower (R:ℝ) : ℝ := ((2*R)^4/2)*lowerConstant
def geometricUpper (R:ℝ) : ℝ := ((2*R)^4/2)*upperConstant

theorem geometricLower_pos {R:ℝ} (hR:0<R) : 0<geometricLower R :=
  mul_pos (by positivity) lowerConstant_pos
theorem geometricUpper_pos {R:ℝ} (hR:0<R) : 0<geometricUpper R :=
  mul_pos (by positivity) upperConstant_pos

/-- Actual full sharp-cube frequency, uniformly in all approach directions.
The eight corner points themselves have frequency zero by the original
fiber theorem; this inequality covers the punctured layer. -/
theorem geometricFrequency_corner_scale {R:ℝ} (hR:0<R) {k:E}
    (hk:k∈ResonantMeasure.cube R) (he0:0<cornerDepth R k)
    (he1:cornerDepth R k≤(1:ℝ)/256) :
    geometricLower R*(cornerDepth R k)^2*(Real.log (1/cornerDepth R k))^2≤
      geometricFrequency R k ∧
    geometricFrequency R k≤geometricUpper R*(cornerDepth R k)^2*
      (Real.log (1/cornerDepth R k))^2 := by
  have hb := sumDensity_zero_two_sided (cornerCoordinates R k)
    (fun i=>(cornerCoordinates_bounds hR k hk i).1)
    (le_maxDeficit _) (maxDeficit_attained _) he0 he1
  rw [geometricFrequency_eq_convolution_real hR hk]
  constructor
  · exact (show geometricLower R*(cornerDepth R k)^2*(Real.log (1/cornerDepth R k))^2=
      ((2*R)^4/2)*(lowerConstant*(cornerDepth R k)^2*(Real.log (1/cornerDepth R k))^2)
      by unfold geometricLower; ring).le.trans (mul_le_mul_of_nonneg_left hb.1 (by positivity))
  · exact (mul_le_mul_of_nonneg_left hb.2 (show 0≤(2*R)^4/2 by positivity)).trans_eq
      (by unfold geometricUpper cornerDepth; ring)

def referenceLower (R:ℝ) : ℝ := ((1+9*R^2)⁻¹)^3*geometricLower R
def referenceUpper (R:ℝ) : ℝ := (1+9*R^2)*geometricUpper R

theorem referenceLower_pos {R:ℝ} (hR:0<R) : 0<referenceLower R :=
  mul_pos (by positivity) (geometricLower_pos hR)
theorem referenceUpper_pos {R:ℝ} (hR:0<R) : 0<referenceUpper R :=
  mul_pos (by positivity) (geometricUpper_pos hR)

/-- The same bounds for the fixed Rayleigh--Jeans reference frequency;
its three weighted source legs and external inverse are retained. -/
theorem referenceFrequency_corner_scale {R:ℝ} (hR:0<R) {k:E}
    (hk:k∈ResonantMeasure.cube R) (he0:0<cornerDepth R k)
    (he1:cornerDepth R k≤(1:ℝ)/256) :
    referenceLower R*(cornerDepth R k)^2*(Real.log (1/cornerDepth R k))^2≤
      referenceFrequency R k ∧
    referenceFrequency R k≤referenceUpper R*(cornerDepth R k)^2*
      (Real.log (1/cornerDepth R k))^2 := by
  have hg := geometricFrequency_corner_scale hR hk he0 he1
  have hn := referenceFrequency_geometric_bounds hR.le hk
  constructor
  · exact (show referenceLower R*(cornerDepth R k)^2*(Real.log (1/cornerDepth R k))^2=
      ((1+9*R^2)⁻¹)^3*(geometricLower R*(cornerDepth R k)^2*
        (Real.log (1/cornerDepth R k))^2) by unfold referenceLower; ring).le.trans
      ((mul_le_mul_of_nonneg_left hg.1 (by positivity)).trans hn.1)
  · exact (hn.2.trans (mul_le_mul_of_nonneg_left hg.2 (by positivity))).trans_eq
      (by unfold referenceUpper; ring)

end
end Resonance.CornerFrequencyBounds
