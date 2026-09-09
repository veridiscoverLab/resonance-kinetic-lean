import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-! The actual frequency/clock weights, including zero frequency. -/
namespace Resonance.FourierCompensationWeights
noncomputable section

def rate (c r : ℝ) : ℝ := c*r^2/(c^2+r^2)
def alpha (η c r : ℝ) : ℝ := η*c*r/(c^2+r^2)
def damping (c r : ℝ) : ℝ := r^2/c

theorem denominator_pos {c : ℝ} (hc : 0<c) (r : ℝ) : 0<c^2+r^2 := by positivity

theorem weight_nonnegative {η c r : ℝ} (hη : 0≤η) (hc : 0<c) (hr : 0≤r) :
    0≤rate c r ∧ 0≤alpha η c r ∧ 0≤damping c r := by
  unfold rate alpha damping
  exact ⟨by positivity,by positivity,by positivity⟩

theorem alpha_times_frequency (η c r : ℝ) : alpha η c r*r=η*rate c r := by
  unfold alpha rate
  ring

theorem rate_le_damping {c : ℝ} (hc : 0<c) (r : ℝ) : rate c r≤damping c r := by
  unfold rate damping
  apply (div_le_div_iff₀ (denominator_pos hc r) hc).mpr
  nlinarith [sq_nonneg (r^2)]

theorem alpha_le_half {η c : ℝ} (hη : 0≤η) (hc : 0<c) (r : ℝ) :
    alpha η c r≤η/2 := by
  unfold alpha
  apply (div_le_iff₀ (denominator_pos hc r)).mpr
  nlinarith [mul_nonneg hη (sq_nonneg (c-r))]

theorem cross_weight_square (η r : ℝ) {c : ℝ} (hc : 0<c) :
    (alpha η c r*damping c r)^2≤η*damping c r*(alpha η c r*r) := by
  have hden := denominator_pos hc r
  have h1 : (alpha η c r*damping c r)^2=η^2*r^6/(c^2+r^2)^2 := by
    unfold alpha damping
    field_simp
  have h2 : η*damping c r*(alpha η c r*r)=η^2*r^4/(c^2+r^2) := by
    unfold alpha damping
    field_simp
  rw [h1,h2]
  apply (div_le_div_iff₀ (sq_pos_of_pos hden) hden).mpr
  nlinarith [show 0≤η^2*r^4*c^2*(c^2+r^2) by positivity]

theorem zero_frequency (η c : ℝ) :
    rate c 0=0 ∧ alpha η c 0=0 ∧ damping c 0=0 := by
  simp [rate,alpha,damping]

theorem weighted_young {a : ℝ} (ha : 0<a) (z x y : ℝ) :
    2*z*x*y≤a*x^2+(z^2/a)*y^2 := by
  apply le_of_mul_le_mul_left (a:=a) ?_ ha
  have he : a*(z^2/a)=z^2 := mul_div_cancel₀ _ ha.ne'
  nlinarith [sq_nonneg (a*x-z*y)]

end
end Resonance.FourierCompensationWeights
