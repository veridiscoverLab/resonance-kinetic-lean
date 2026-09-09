import Resonance.HilbertCurrentConvergence
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-! Weak convergence with a strongly converging test. This is the step used
when the four-leg mobility varies: strong convergence is only requested on
fixed adjoint tests, never on the unknown microscopic sequence. -/
open Filter
open scoped Topology
namespace Resonance.HilbertMovingTest
variable {ι E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
variable {l : Filter ι} {x : ι→E} {u v : E} {test : ι→E}

theorem weak_moving_test {C : ℝ} (hbound : ∀ n,‖x n‖≤C)
    (hweak : ∀ w:E,Tendsto (fun n=>inner ℝ (x n) w) l (𝓝 (inner ℝ u w)))
    (htest : Tendsto test l (𝓝 v)) :
    Tendsto (fun n=>inner ℝ (x n) (test n)) l (𝓝 (inner ℝ u v)) := by
  have herr : Tendsto (fun n=>inner ℝ (x n) (test n-v)) l (𝓝 (0:ℝ)) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    have hle : ∀n,‖inner ℝ (x n) (test n-v)‖≤C*‖test n-v‖ := by
      intro n
      calc
        ‖inner ℝ (x n) (test n-v)‖≤‖x n‖*‖test n-v‖:=norm_inner_le_norm _ _
        _≤C*‖test n-v‖:=mul_le_mul_of_nonneg_right (hbound n) (norm_nonneg _)
    exact squeeze_zero (fun n=>norm_nonneg _) hle
      (by simpa using (tendsto_iff_norm_sub_tendsto_zero.mp htest).const_mul C)
  have hh:=herr.add (hweak v)
  have heq : (fun n=>inner ℝ (x n) (test n-v)+inner ℝ (x n) v)=
      (fun n=>inner ℝ (x n) (test n)) := by
    funext n
    rw [inner_sub_right]
    ring
  simpa only [heq,zero_add] using hh

theorem weak_images [CompleteSpace E] [CompleteSpace F]
    {C : ℝ} (hbound : ∀ n,‖x n‖≤C)
    (hweak : ∀ w:E,Tendsto (fun n=>inner ℝ (x n) w) l (𝓝 (inner ℝ u w)))
    (T : ι→E→L[ℝ]F) (S : E→L[ℝ]F)
    (hfixed : ∀ w:F,Tendsto (fun n=>(T n).adjoint w) l (𝓝 (S.adjoint w))) :
    ∀ w:F,Tendsto (fun n=>inner ℝ (T n (x n)) w) l (𝓝 (inner ℝ (S u) w)) := by
  intro w
  have hh:=weak_moving_test hbound hweak (hfixed w)
  simpa only [ContinuousLinearMap.adjoint_inner_right] using hh

end Resonance.HilbertMovingTest
