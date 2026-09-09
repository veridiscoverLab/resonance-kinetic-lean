import Resonance.CornerInverseFrequency

/-! A single depth function controls distances between every pair of
corner layers, even when the two points approach different corners. -/
open Real Set MeasureTheory
namespace Resonance.CornerDepthLipschitz
noncomputable section
set_option maxHeartbeats 500000
open Resonance.PlaneCoarea Resonance.CornerFrequencyBounds
open Resonance.CubeFrequencyReflection Resonance.CriticalLogShells

theorem coordinate_depth_difference {R:ℝ} (hR:0<R) (k p:E) (i:Fin 3) :
    cornerCoordinates R k i-cornerCoordinates R p i≤‖k-p‖/(2*R) := by
  have ha : |p i|-|k i|≤|p i-k i| := abs_sub_abs_le_abs_sub (p i) (k i)
  have hb : |p i-k i|≤‖k-p‖ := by
    rw [abs_sub_comm]
    have h := PiLp.norm_apply_le (k-p) i
    simpa only [Real.norm_eq_abs,PiLp.sub_apply] using h
  have he : cornerCoordinates R k i-cornerCoordinates R p i=
      (|p i|-|k i|)/(2*R) := by unfold cornerCoordinates; ring
  rw [he]
  exact div_le_div_of_nonneg_right (ha.trans hb) (by positivity)

theorem depth_difference {R:ℝ} (hR:0<R) (k p:E) :
    cornerDepth R k-cornerDepth R p≤‖k-p‖/(2*R) := by
  obtain ⟨i,hi⟩ := maxDeficit_attained (cornerCoordinates R k)
  have hd := coordinate_depth_difference hR k p i
  have hp := le_maxDeficit (cornerCoordinates R p) i
  change cornerCoordinates R k i=cornerDepth R k at hi
  change cornerCoordinates R p i≤cornerDepth R p at hp
  linarith

theorem depth_abs_difference {R:ℝ} (hR:0<R) (k p:E) :
    |cornerDepth R k-cornerDepth R p|≤‖k-p‖/(2*R) := by
  rw [abs_le]
  constructor
  · have h := depth_difference hR p k
    rw [norm_sub_rev] at h
    linarith
  · exact depth_difference hR k p

theorem shellRadius_add (n m:ℕ) :
    shellRadius (n+m)=Real.exp (-(m:ℝ))*shellRadius n := by
  unfold shellRadius
  rw [←Real.exp_add]
  congr 1
  push_cast
  ring

theorem shellRadius_antitone : Antitone shellRadius := by
  intro n m hnm
  unfold shellRadius
  apply Real.exp_le_exp.mpr
  have h : (n:ℝ) ≤ m := by exact_mod_cast hnm
  linarith

def separationConstant (R:ℝ) : ℝ := 2*R*(Real.exp (-1)-Real.exp (-2))

theorem separationConstant_pos {R:ℝ} (hR:0<R) : 0<separationConstant R := by
  unfold separationConstant
  exact mul_pos (by positivity) (sub_pos.mpr (Real.exp_lt_exp.mpr (by norm_num)))

theorem separated_shell_distance {R:ℝ} (hR:0<R) {k p:E} {j l:ℕ}
    (hj:k∈shell (cornerDepth R) j) (hl:p∈shell (cornerDepth R) l) (hjl:j+2≤l) :
    separationConstant R*shellRadius j≤‖k-p‖ := by
  have hp := hl.2.trans (shellRadius_antitone hjl)
  have hk := hj.1.le
  rw [shellRadius_add] at hp hk
  norm_num only [Nat.cast_ofNat,Nat.cast_one] at hp hk
  have hd := depth_difference hR k p
  have hm := (le_div_iff₀ (show 0<2*R by positivity)).mp hd
  unfold separationConstant
  nlinarith

end
end Resonance.CornerDepthLipschitz
