import Resonance.FourierExponentialDecay
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

/-! Simultaneous summation of all vector modes with nonnegative Sobolev
weights. The extended sum is used before proving finiteness; a divergent
sum is never silently replaced by zero. -/
open scoped ENNReal
namespace Resonance.FourierEnergySummation
noncomputable section
open FourierCompensationWeights
variable {I E : Type*} [NormedAddCommGroup E]

def energy (w : I→ℝ) (v : I→E) : ℝ≥0∞ := ∑'i,ENNReal.ofReal (w i*‖v i‖^2)

theorem energy_comparison (w : I→ℝ) (hw : ∀i,0≤w i) {u v : I→E} {C : ℝ}
    (hb : ∀i,‖u i‖^2≤C*‖v i‖^2) :
    energy w u≤ENNReal.ofReal C*energy w v := by
  unfold energy
  rw [←ENNReal.tsum_mul_left]
  apply ENNReal.tsum_le_tsum
  intro i
  calc
    _ ≤ ENNReal.ofReal (C*(w i*‖v i‖^2)) := by
      apply ENNReal.ofReal_le_ofReal
      have hh := mul_le_mul_of_nonneg_left (hb i) (hw i)
      nlinarith
    _ = _ := ENNReal.ofReal_mul' (mul_nonneg (hw i) (sq_nonneg _))

theorem energy_finite_of_comparison (w : I→ℝ) (hw : ∀i,0≤w i) {u v : I→E} {C : ℝ}
    (hb : ∀i,‖u i‖^2≤C*‖v i‖^2) (hv : energy w v≠∞) : energy w u≠∞ := by
  exact ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hv)
    (energy_comparison w hw hb)

theorem rate_lower_nonzero {c r : ℝ} (hc : 0<c) (hr : 1≤r) :
    c/(c^2+1)≤rate c r := by
  have hd : 0<c^2+1 := by positivity
  unfold rate
  apply (div_le_div_iff₀ hd (denominator_pos hc r)).mpr
  have hs : 1≤r^2 := by nlinarith
  have hh := mul_nonneg (show 0≤c*c*c by positivity) (sub_nonneg.mpr hs)
  nlinarith

theorem simultaneous_decay (w : I→ℝ) (hw : ∀i,0≤w i) {u v : I→E}
    {a c t : ℝ} (ha : 0≤a) (hc : 0<c) (ht : 0≤t) (r : I→ℝ)
    (hr : ∀i,1≤r i)
    (hb : ∀i,‖u i‖^2≤3*Real.exp (-a*rate c (r i)*t)*‖v i‖^2) :
    energy w u≤ENNReal.ofReal (3*Real.exp (-a*(c/(c^2+1))*t))*energy w v := by
  apply energy_comparison w hw
  intro i
  have hh := mul_le_mul_of_nonneg_right (rate_lower_nonzero hc (hr i)) (mul_nonneg ha ht)
  have he : Real.exp (-a*rate c (r i)*t)≤Real.exp (-a*(c/(c^2+1))*t) := by
    apply Real.exp_le_exp.mpr
    nlinarith
  have hm := mul_le_mul_of_nonneg_right he (show 0≤3*‖v i‖^2 by positivity)
  nlinarith [hb i]

end
end Resonance.FourierEnergySummation
