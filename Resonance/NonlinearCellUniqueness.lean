import Resonance.NonlinearRegularizedCell
import Resonance.ContinuousLinearizedUniqueness

/-! Uniform small-amplitude uniqueness for the actual full nonlinear
cell. The amplitude restriction is in C(D); no hidden B_s bound is imposed
on competing solutions. -/
open Set
namespace Resonance.NonlinearCellUniqueness
noncomputable section
set_option maxHeartbeats 2200000
open ResonantMeasure Thermodynamics ProfileBanachSmooth RegularizedGraphNorm
open ContinuousSourceCoordinates PhysicalMomentProjection NormalizedCubicRemainder
open ContinuousRegularizedEquation ContinuousResolventBounds NonlinearRegularizedStep
open ContinuousLinearizedUniqueness

theorem actual_solution_fixed_point {R : ℝ} (hR : 0<R) {θ : Parameter}
    (hθ : θ∈positiveDomain R) {s : ℝ} (hs : 1 ≤ s) (q F : X R)
    (hF : projection hR hθ (sourceMap hR F)=0)
    (he : q-s • (denominatorMap R θ*FiberContinuity.collisionMap R hR.le
      (profileMap R θ*(1+q)))=F) :
    step hR hθ hs F (lift hR.le s q)=lift hR.le s q := by
  rw [actual_normalized_decomposition hR.le hθ,smul_add,←sub_sub] at he
  have hel : q-s • linearAction hR.le θ q=F+s • remainder R hR.le θ q :=
    sub_eq_iff_eq_add.mp he
  have hout := original_solution_eq_output hR hθ (zero_lt_one.trans_le hs) q
    (F+s • remainder R hR.le θ q) (step_source_micro hR hθ hs F (lift hR.le s q) hF) hel
  apply read_injective
  change output hR hθ (zero_lt_one.trans_le hs) (F+s • remainder R hR.le θ q)=q
  exact hout.symm

theorem actual_small_nonlinear_cell_unique {R : ℝ} (hR : 0<R) {K : Set Parameter}
    (hK : IsCompact K) (hpos : K⊆positiveDomain R) :
    ∃κ : ℝ,0<κ ∧ ∀θ,(hθ : θ∈K) → ∀s : ℝ,(hs : 1 ≤ s) → ∀F q r : X R,
      projection hR (hpos hθ) (sourceMap hR F)=0 → ‖q‖≤κ → ‖r‖≤κ →
      q-s • (denominatorMap R θ*FiberContinuity.collisionMap R hR.le (profileMap R θ*(1+q)))=F →
      r-s • (denominatorMap R θ*FiberContinuity.collisionMap R hR.le (profileMap R θ*(1+r)))=F → q=r := by
  obtain ⟨A,hA,hlin⟩ := actual_graph_resolvent_bound hR hK hpos
  obtain ⟨B,hB,hrem⟩ := actual_compact_remainder_oneY hR hK hpos
  let κ : ℝ := min 1 (1/(2*A*B))
  have hκ : 0<κ := lt_min zero_lt_one (by positivity)
  have hκ1 : κ≤1 := min_le_left _ _
  have hsmall : A*B*κ≤(1/2:ℝ) := by
    calc
      _≤A*B*(1/(2*A*B)) := mul_le_mul_of_nonneg_left (min_le_right _ _) (by positivity)
      _=_ := by field_simp [hA.ne',hB.ne']
  refine ⟨κ,hκ,?_⟩
  intro θ hθ s hs F q r hF hq hr heq her
  have hqf := actual_solution_fixed_point hR (hpos hθ) (s:=s) hs q F hF heq
  have hrf := actual_solution_fixed_point hR (hpos hθ) (s:=s) hs r F hF her
  have hb := step_difference_bound hR (hpos hθ) hs hA.le hB.le hκ.le
    (hlin θ hθ s hs) F (lift hR.le s q) (lift hR.le s r)
    (hrem θ hθ κ hκ1 q r hq hr)
  rw [hqf,hrf] at hb
  have hh := hb.trans (mul_le_mul_of_nonneg_right hsmall (norm_nonneg _))
  have hz : lift hR.le s q=lift hR.le s r :=
    sub_eq_zero.mp (norm_eq_zero.mp (by nlinarith [norm_nonneg (lift hR.le s q-lift hR.le s r)]))
  exact congrArg read hz

theorem actual_unique_small_cell_branch {R : ℝ} (hR : 0<R) {K : Set Parameter}
    (hK : IsCompact K) (hpos : K⊆positiveDomain R) :
    ∃δ C κ : ℝ,0<δ ∧ 0<C ∧ 0<κ ∧ ∀θ,(hθ : θ∈K) → ∀s : ℝ,(hs : 1 ≤ s) →
      ∀F : X R,‖F‖≤δ → projection hR (hpos hθ) (sourceMap hR F)=0 →
      ∃q : X R,
        q-s • (denominatorMap R θ*FiberContinuity.collisionMap R hR.le (profileMap R θ*(1+q)))=F ∧
        projection hR (hpos hθ) (sourceMap hR q)=0 ∧
        ‖q‖≤C*‖F‖ ∧ s*‖OneWeightedPairReadout.referenceContinuous hR.le*q‖≤C*‖F‖ ∧
        ‖q‖≤κ ∧
        ∀r : X R,‖r‖≤κ →
          r-s • (denominatorMap R θ*FiberContinuity.collisionMap R hR.le (profileMap R θ*(1+r)))=F → r=q := by
  obtain ⟨δ,C,hδ,hC,hex⟩ := NonlinearRegularizedCell.actual_nonlinear_regularized_cell hR hK hpos
  obtain ⟨κ,hκ,hu⟩ := actual_small_nonlinear_cell_unique hR hK hpos
  refine ⟨min δ (κ/C),C,κ,lt_min hδ (div_pos hκ hC),hC,hκ,?_⟩
  intro θ hθ s hs F hFn hF
  obtain ⟨q,he,hm,hq,hw,_⟩ := hex θ hθ s hs F (hFn.trans (min_le_left _ _)) hF
  have hqκ : ‖q‖≤κ := hq.trans ((mul_le_mul_of_nonneg_left
    (hFn.trans (min_le_right _ _)) hC.le).trans_eq (by field_simp [hC.ne']))
  exact ⟨q,he,hm,hq,hw,hqκ,fun r hr her=>hu θ hθ s hs F r q hF hr hqκ her he⟩

end
end Resonance.NonlinearCellUniqueness
