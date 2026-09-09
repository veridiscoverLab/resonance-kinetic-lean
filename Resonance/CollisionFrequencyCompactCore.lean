import Resonance.CollisionFrequencyPositive

/-! Strict lower bounds for the original reference frequency on any
closed part of the cube separated from its eight corners. -/
open Real Set MeasureTheory
open scoped Topology
namespace Resonance.CollisionFrequencyCompactCore
noncomputable section
open Resonance.PlaneCoarea Resonance.CollisionFrequency
open Resonance.CollisionFrequencyPositive Resonance.FiberContinuity

def cornerRadius (R:ℝ) (k:E) : ℝ :=
  max (R-|k 0|) (max (R-|k 1|) (R-|k 2|))

theorem cornerRadius_continuous (R:ℝ) : Continuous (cornerRadius R) := by
  unfold cornerRadius
  fun_prop

theorem cornerRadius_corner_zero {R:ℝ} {k:E} (hk:isCubeCorner R k) :
    cornerRadius R k=0 := by
  simp [cornerRadius,hk 0,hk 1,hk 2]

theorem cornerRadius_coordinate_le (R:ℝ) (k:E) (i:Fin 3) : R-|k i|≤cornerRadius R k := by
  fin_cases i
  · exact le_max_left _ _
  · exact (le_max_left _ _).trans (le_max_right _ _)
  · exact (le_max_right _ _).trans (le_max_right _ _)

theorem cornerRadius_attained (R:ℝ) (k:E) : ∃i:Fin 3,R-|k i|=cornerRadius R k := by
  by_cases h0:max (R-|k 1|) (R-|k 2|)≤R-|k 0|
  · exact ⟨0,by simp [cornerRadius,max_eq_left h0]⟩
  · by_cases h1:R-|k 2|≤R-|k 1|
    · exact ⟨1,by rw [cornerRadius,max_eq_right (le_of_not_ge h0),max_eq_left h1]⟩
    · exact ⟨2,by rw [cornerRadius,max_eq_right (le_of_not_ge h0),max_eq_right (le_of_not_ge h1)]⟩

def compactCore (R η:ℝ) : Set E := ResonantMeasure.cube R∩{k | η≤cornerRadius R k}

theorem compactCore_isCompact (R η:ℝ) : IsCompact (compactCore R η) :=
  (cube_isCompact R).inter_right (isClosed_le continuous_const (cornerRadius_continuous R))

theorem geometricFrequency_compactCore_lower {R η:ℝ} (hR:0<R) (hη:0<η) :
    ∃m:ℝ,0 < m ∧ ∀k∈ResonantMeasure.cube R,η≤cornerRadius R k→m≤geometricFrequency R k := by
  by_cases hn:(compactCore R η).Nonempty
  · obtain ⟨k,hk,hmin⟩ := (compactCore_isCompact R η).exists_isMinOn hn
      ((geometricFrequency_continuousOn hR.le).mono inter_subset_left)
    have hp : 0<geometricFrequency R k := geometricFrequency_noncorner_positive hR hk.1
      (fun h=>by
        have he:=cornerRadius_corner_zero h
        have hηk : η≤cornerRadius R k := hk.2
        linarith)
    exact ⟨geometricFrequency R k,hp,fun p hp hηp=>hmin ⟨hp,hηp⟩⟩
  · refine ⟨1,by norm_num,?_⟩
    intro k hk hηk
    exact (hn ⟨k,hk,hηk⟩).elim

theorem referenceFrequency_compactCore_lower {R η:ℝ} (hR:0<R) (hη:0<η) :
    ∃m:ℝ,0 < m ∧ ∀k∈ResonantMeasure.cube R,η≤cornerRadius R k→m≤referenceFrequency R k := by
  obtain ⟨m,hm,hbound⟩ := geometricFrequency_compactCore_lower hR hη
  refine ⟨(1+9*R^2)⁻¹^3*m,mul_pos (by positivity) hm,?_⟩
  intro k hk hηk
  exact (mul_le_mul_of_nonneg_left (hbound k hk hηk) (by positivity)).trans
    (referenceFrequency_geometric_bounds hR.le hk).1

end
end Resonance.CollisionFrequencyCompactCore
