import Resonance.HilbertMovingTest

/-! Fixed-test convergence propagates through uniformly bounded operators.
The sandwich identity keeps both coefficient factors and the same complete
difference operator. No strong convergence of the unknown source is used. -/
open Filter
open scoped Topology
namespace Resonance.HilbertOperatorConvergence
variable {ι E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
variable {l : Filter ι}

theorem strong_on_moving {v : ι→E} {u : E}
    (B : ι→E→L[ℝ]F) (S : E→L[ℝ]F) {C : ℝ}
    (hbound : ∀n,‖B n‖≤C)
    (hfixed : ∀w:E,Tendsto (fun n=>B n w) l (𝓝 (S w)))
    (hv : Tendsto v l (𝓝 u)) : Tendsto (fun n=>B n (v n)) l (𝓝 (S u)) := by
  have hz : Tendsto (fun n=>B n (v n-u)) l (𝓝 (0:F)) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    have hle : ∀n,‖B n (v n-u)‖≤C*‖v n-u‖ := by
      intro n
      exact ((B n).le_opNorm _).trans
        (mul_le_mul_of_nonneg_right (hbound n) (norm_nonneg _))
    exact squeeze_zero (fun n=>norm_nonneg _) hle
      (by simpa using (tendsto_iff_norm_sub_tendsto_zero.mp hv).const_mul C)
  have hh:=hz.add (hfixed u)
  simpa only [map_sub,sub_add_cancel,zero_add] using hh

theorem weak_symmetric_images
    {x : ι→E} {u : E} {C : ℝ} (hbound : ∀n,‖x n‖≤C)
    (hweak : ∀w:E,Tendsto (fun n=>inner ℝ (x n) w) l (𝓝 (inner ℝ u w)))
    (B : ι→E→L[ℝ]E) (S : E→L[ℝ]E)
    (hsym : ∀n x y,inner ℝ (B n x) y=inner ℝ x (B n y))
    (hsymS : ∀x y,inner ℝ (S x) y=inner ℝ x (S y))
    (hfixed : ∀w:E,Tendsto (fun n=>B n w) l (𝓝 (S w))) :
    ∀w:E,Tendsto (fun n=>inner ℝ (B n (x n)) w) l (𝓝 (inner ℝ (S u) w)) := by
  intro w
  simpa only [hsym,hsymS] using HilbertMovingTest.weak_moving_test hbound hweak (hfixed w)

theorem weak_sandwich [CompleteSpace E] [CompleteSpace F]
    {x : ι→E} {u : E} {Cx CB : ℝ}
    (hx : ∀n,‖x n‖≤Cx)
    (hweak : ∀w:E,Tendsto (fun n=>inner ℝ (x n) w) l (𝓝 (inner ℝ u w)))
    (R : E→L[ℝ]F) (B : ι→E→L[ℝ]E) (B0 : E→L[ℝ]E)
    (A : ι→F→L[ℝ]F) (A0 : F→L[ℝ]F)
    (hB : ∀n,‖B n‖≤CB)
    (hBs : ∀n x y,inner ℝ (B n x) y=inner ℝ x (B n y))
    (hB0s : ∀x y,inner ℝ (B0 x) y=inner ℝ x (B0 y))
    (hAs : ∀n x y,inner ℝ (A n x) y=inner ℝ x (A n y))
    (hA0s : ∀x y,inner ℝ (A0 x) y=inner ℝ x (A0 y))
    (hBfixed : ∀w:E,Tendsto (fun n=>B n w) l (𝓝 (B0 w)))
    (hAfixed : ∀w:F,Tendsto (fun n=>A n w) l (𝓝 (A0 w))) :
    ∀w:F,Tendsto (fun n=>inner ℝ (A n (R (B n (x n)))) w) l
      (𝓝 (inner ℝ (A0 (R (B0 u))) w)) := by
  intro w
  have ht : Tendsto (fun n=>B n (R.adjoint (A n w))) l
      (𝓝 (B0 (R.adjoint (A0 w)))) :=
    strong_on_moving B B0 hB hBfixed (R.adjoint.continuous.tendsto _ |>.comp (hAfixed w))
  have hh:=HilbertMovingTest.weak_moving_test hx hweak ht
  simpa only [←hBs,←hB0s,ContinuousLinearMap.adjoint_inner_right,←hAs,←hA0s] using hh

end Resonance.HilbertOperatorConvergence
