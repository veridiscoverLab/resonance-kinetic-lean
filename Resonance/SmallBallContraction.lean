import Mathlib.Topology.MetricSpace.Contracting
import Mathlib.Analysis.Normed.Module.Basic

/-! A closed-ball version of the proved Banach contraction theorem. -/
open Set
open scoped NNReal
namespace Resonance.SmallBallContraction
noncomputable section

theorem exists_fixed_point {E : Type*} [NormedAddCommGroup E] [CompleteSpace E]
    (T : E→E) {r : ℝ} (hr : 0≤r) (h0 : ‖T 0‖≤r/2)
    (hL : ∀x y : E,‖x‖≤r → ‖y‖≤r → ‖T x-T y‖≤(1/2:ℝ)*‖x-y‖) :
    ∃x : E,‖x‖≤r ∧ T x=x := by
  let S := Metric.closedBall (0:E) r
  have hmem (x : E) : x∈S ↔ ‖x‖≤r := by simp only [S,Metric.mem_closedBall,dist_zero_right]
  have hm : MapsTo T S S := by
    intro x hx
    apply (hmem _).mpr
    have hh := hL x 0 ((hmem x).mp hx) (by simpa using hr)
    have hn := norm_add_le (T x-T 0) (T 0)
    simp only [sub_add_cancel,sub_zero] at hh hn
    linarith [(hmem x).mp hx]
  have hc : ContractingWith (1/2:ℝ≥0) (hm.restrict T S S) := by
    refine ⟨by norm_num,?_⟩
    apply LipschitzWith.of_dist_le_mul
    intro x y
    change dist (T x.val) (T y.val)≤((1/2:ℝ≥0):ℝ)*dist x.val y.val
    simpa only [dist_eq_norm,NNReal.coe_div,NNReal.coe_one,NNReal.coe_ofNat] using
      hL x y ((hmem x).mp x.property) ((hmem y).mp y.property)
  obtain ⟨x,hx,hfix,_⟩ := ContractingWith.exists_fixedPoint'
    (Metric.isClosed_closedBall.isComplete) hm hc ((hmem 0).mpr (by simpa using hr))
      (edist_ne_top (0:E) (T 0))
  exact ⟨x,(hmem x).mp hx,hfix⟩

end
end Resonance.SmallBallContraction
