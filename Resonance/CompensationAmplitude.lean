import Mathlib.Tactic

/-! A compensation amplitude chosen once from the coercivity and operator
budgets, independently of Fourier frequency and collision clock. -/
namespace Resonance.CompensationAmplitude
noncomputable section

def crossBudget (L : ℝ) : ℝ := 1+8*L^2
def amplitude (β k L : ℝ) : ℝ :=
  min 1 (min (1/(1+4*L)) (min (k*β/(1+4*(crossBudget L)^2)) (β/(1+4*crossBudget L))))

theorem amplitude_bounds {β k L : ℝ} (hβ : 0<β) (hk : 0<k) (hL : 0≤L) :
    0<amplitude β k L ∧ amplitude β k L≤1 ∧
      amplitude β k L*(4*L)≤1 ∧
      4*(crossBudget L)^2*amplitude β k L≤k*β ∧
      4*crossBudget L*amplitude β k L≤β := by
  have hM : 0<crossBudget L := by unfold crossBudget;positivity
  have hp1 : 0<1+4*L := by positivity
  have hp2 : 0<1+4*(crossBudget L)^2 := by positivity
  have hp3 : 0<1+4*crossBudget L := by positivity
  have hη : 0<amplitude β k L := by
    unfold amplitude
    exact lt_min (by norm_num) (lt_min (by positivity) (lt_min (by positivity) (by positivity)))
  have h1 : amplitude β k L≤1/(1+4*L) :=
    (min_le_right _ _).trans (min_le_left _ _)
  have h2 : amplitude β k L≤k*β/(1+4*(crossBudget L)^2) :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have h3 : amplitude β k L≤β/(1+4*crossBudget L) :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  have hh1 := (le_div_iff₀ hp1).mp h1
  have hh2 := (le_div_iff₀ hp2).mp h2
  have hh3 := (le_div_iff₀ hp3).mp h3
  exact ⟨hη,min_le_left _ _,by nlinarith,by nlinarith,by nlinarith⟩

end
end Resonance.CompensationAmplitude
