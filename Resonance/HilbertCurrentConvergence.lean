import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! Strong convergence from the actual Hilbert norm budget and the pairing
with the one fixed limiting vector. The weak/entropy premises must be proved
for the original current by the model-specific front end. -/
open Filter
open scoped Topology
namespace Resonance.HilbertCurrentConvergence
variable {ι E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {l : Filter ι} {v : ι→E} {u : E}

theorem strong_of_norm_square_and_pairing
    (hn : Tendsto (fun n=>‖v n‖^2) l (𝓝 (‖u‖^2)))
    (hi : Tendsto (fun n=>inner ℝ (v n) u) l (𝓝 (‖u‖^2))) :
    Tendsto v l (𝓝 u) := by
  have hs : Tendsto (fun n=>‖v n-u‖^2) l (𝓝 (0:ℝ)) := by
    have h:= (hn.sub (hi.const_mul 2)).add_const (‖u‖^2)
    simpa only [norm_sub_sq_real,show ‖u‖^2-2*‖u‖^2+‖u‖^2=0 by ring] using h
  have hh:=Real.continuous_sqrt.continuousAt.tendsto.comp hs
  change Tendsto (fun n=>Real.sqrt (‖v n-u‖^2)) l (𝓝 (Real.sqrt 0)) at hh
  have heq : (fun n=>Real.sqrt (‖v n-u‖^2))=(fun n=>‖v n-u‖) := by
    funext n
    exact Real.sqrt_sq (norm_nonneg _)
  rw [heq,Real.sqrt_zero] at hh
  exact tendsto_iff_norm_sub_tendsto_zero.mpr hh

theorem strong_of_weak_and_norm_square
    (hw : ∀w:E,Tendsto (fun n=>inner ℝ (v n) w) l (𝓝 (inner ℝ u w)))
    (hn : Tendsto (fun n=>‖v n‖^2) l (𝓝 (‖u‖^2))) : Tendsto v l (𝓝 u) := by
  apply strong_of_norm_square_and_pairing hn
  simpa only [real_inner_self_eq_norm_sq] using hw u

end Resonance.HilbertCurrentConvergence
