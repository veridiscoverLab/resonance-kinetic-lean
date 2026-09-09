import Resonance.NonlinearRegularizedStep
import Resonance.SmallBallContraction

/-! Existence of the original small nonlinear regularized cell, uniformly
over every compact positive RJ parameter set and every collision scale s≥1.
The proof uses the actual full cubic and its one-weighted-input estimate. -/
open Set
namespace Resonance.NonlinearRegularizedCell
noncomputable section
set_option maxHeartbeats 2500000
open ResonantMeasure Thermodynamics ProfileBanachSmooth
open RegularizedGraphNorm ContinuousRegularizedEquation ContinuousResolventBounds
open NormalizedCubicRemainder NonlinearRegularizedStep OneWeightedPairReadout
open ContinuousSourceCoordinates PhysicalMomentProjection

theorem actual_nonlinear_regularized_cell {R : ℝ} (hR : 0<R) {K : Set Parameter}
    (hK : IsCompact K) (hpos : K⊆positiveDomain R) :
    ∃δ C : ℝ,0<δ ∧ 0<C ∧ ∀θ,(hθ : θ∈K) → ∀s,(hs : 1 ≤ s) →
      ∀F : X R,‖F‖≤δ → projection hR (hpos hθ) (sourceMap hR F)=0 →
      ∃q : X R,
        q-s • (denominatorMap R θ*FiberContinuity.collisionMap R hR.le
          (profileMap R θ*(1+q)))=F ∧
        projection hR (hpos hθ) (sourceMap hR q)=0 ∧
        ‖q‖≤C*‖F‖ ∧ s*‖referenceContinuous hR.le*q‖≤C*‖F‖ ∧ ‖q‖≤(1/2:ℝ) := by
  obtain ⟨A,hA,hlin⟩ := actual_graph_resolvent_bound hR hK hpos
  obtain ⟨B,hB,hrem⟩ := actual_compact_remainder_oneY hR hK hpos
  let κ : ℝ := min (1/2) (1/(4*A*B))
  have hκ : 0<κ := lt_min (by norm_num) (by positivity)
  have hκhalf : κ≤(1/2:ℝ) := min_le_left _ _
  have hκ1 : κ≤1 := hκhalf.trans (by norm_num)
  have hAB : 0<A*B := mul_pos hA hB
  have hsmall : A*B*κ≤(1/4:ℝ) := by
    calc
      _≤A*B*(1/(4*A*B)) := mul_le_mul_of_nonneg_left (min_le_right _ _) hAB.le
      _=_ := by field_simp [hA.ne',hB.ne']
  let δ : ℝ := κ/(2*A)
  have hδ : 0<δ := div_pos hκ (by positivity)
  refine ⟨δ,2*A,hδ,by positivity,?_⟩
  intro θ hθ s hs F hFn hF
  letI : CompleteSpace (graphSpace hR.le s) := graph_complete hR.le s
  let r : ℝ := 2*A*‖F‖
  have hr : 0≤r := by dsimp [r]; positivity
  have hrκ : r≤κ := by
    calc
      _≤2*A*δ := mul_le_mul_of_nonneg_left hFn (by positivity)
      _=κ := by dsimp [δ]; field_simp [hA.ne']
  let T := step hR (hpos hθ) hs F
  have hzero : ‖T 0‖≤r/2 := by
    change ‖step hR (hpos hθ) hs F 0‖≤_
    rw [step_zero]
    exact (hlin θ hθ s hs F).trans_eq (by dsimp [r]; ring)
  have hcontract : ∀q t : graphSpace hR.le s,
      ‖q‖≤r → ‖t‖≤r → ‖T q-T t‖≤(1/2:ℝ)*‖q-t‖ := by
    intro q t hq ht
    have hqκ : ‖read q‖≤κ := (read_norm_le q).trans (hq.trans hrκ)
    have htκ : ‖read t‖≤κ := (read_norm_le t).trans (ht.trans hrκ)
    have hb := step_difference_bound hR (hpos hθ) hs hA.le hB.le hκ.le
      (hlin θ hθ s hs) F q t (hrem θ hθ κ hκ1 (read q) (read t) hqκ htκ)
    exact hb.trans (mul_le_mul_of_nonneg_right (hsmall.trans (by norm_num)) (norm_nonneg _))
  obtain ⟨q,hq,hfix⟩ := @SmallBallContraction.exists_fixed_point (graphSpace hR.le s)
    inferInstance (graph_complete hR.le s) T r hr hzero hcontract
  obtain ⟨he,hm⟩ := fixed_point_original_equation hR (hpos hθ) hs F q hF hfix
  exact ⟨read q,he,hm,(read_norm_le q).trans hq,
    (weighted_norm_le (zero_le_one.trans hs) q).trans hq,
    (read_norm_le q).trans (hq.trans (hrκ.trans hκhalf))⟩

end
end Resonance.NonlinearRegularizedCell
