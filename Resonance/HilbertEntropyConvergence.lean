import Resonance.HilbertCurrentConvergence

/-! Weak current convergence and the true nonnegative terminal entropy
give strong current convergence. No vanishing terminal entropy is assumed. -/
open Filter
open scoped Topology
namespace Resonance.HilbertEntropyConvergence
variable {ι E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {l : Filter ι} {v : ι → E} {u : E} {W H : ι → ℝ}

theorem norm_square_of_entropy_upper
    (hi : Tendsto (fun n => inner ℝ (v n) u) l (𝓝 (‖u‖ ^ 2)))
    (hW : Tendsto W l (𝓝 (‖u‖ ^ 2)))
    (hupper : ∀ n, ‖v n‖ ^ 2 ≤ W n) :
    Tendsto (fun n => ‖v n‖ ^ 2) l (𝓝 (‖u‖ ^ 2)) := by
  have hlo : Tendsto (fun n => 2 * inner ℝ (v n) u - ‖u‖ ^ 2) l
      (𝓝 (‖u‖ ^ 2)) := by
    convert (hi.const_mul 2).sub_const (‖u‖ ^ 2) using 1
    congr 1
    ring
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le hlo hW _ hupper
  intro n
  have h := sq_nonneg ‖v n-u‖
  rw [norm_sub_sq_real] at h
  linarith

theorem strong_of_entropy_upper
    (hw : ∀ w : E, Tendsto (fun n => inner ℝ (v n) w) l (𝓝 (inner ℝ u w)))
    (hW : Tendsto W l (𝓝 (‖u‖ ^ 2)))
    (hupper : ∀ n, ‖v n‖ ^ 2 ≤ W n) : Tendsto v l (𝓝 u) := by
  apply HilbertCurrentConvergence.strong_of_weak_and_norm_square hw
  apply norm_square_of_entropy_upper _ hW hupper
  simpa only [real_inner_self_eq_norm_sq] using hw u

theorem strong_and_terminal_of_entropy_equality
    (hw : ∀ w : E, Tendsto (fun n => inner ℝ (v n) w) l (𝓝 (inner ℝ u w)))
    (hW : Tendsto W l (𝓝 (‖u‖ ^ 2)))
    (hH : ∀ n, 0 ≤ H n) (he : ∀ n, ‖v n‖ ^ 2 + H n = W n) :
    Tendsto v l (𝓝 u) ∧ Tendsto H l (𝓝 0) := by
  have hu : ∀ n, ‖v n‖ ^ 2 ≤ W n := fun n => by linarith [hH n,he n]
  have hn := norm_square_of_entropy_upper
    (by simpa only [real_inner_self_eq_norm_sq] using hw u) hW hu
  refine ⟨strong_of_entropy_upper hw hW hu,?_⟩
  have h := hW.sub hn
  have heq : H = fun n => W n - ‖v n‖ ^ 2 := funext (fun n => by linarith [he n])
  rw [heq]
  simpa only [sub_self] using h

end Resonance.HilbertEntropyConvergence
