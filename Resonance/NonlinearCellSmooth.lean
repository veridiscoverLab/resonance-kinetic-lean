import Resonance.GraphResolventSmooth
import Resonance.SmoothContractionImplicit

/-! Smooth local parameter/source branches of the same full nonlinear
cell. The small radius is uniform in every real s ≥ 1. The implicit
derivative is invertible because of the proved one-Y contraction, not a
new invertibility hypothesis. Compatible sources retain all five moments. -/
open Set
open scoped Topology ContDiff
namespace Resonance.NonlinearCellSmooth
noncomputable section
set_option maxHeartbeats 2600000
open ResonantMeasure Thermodynamics ProfileBanachSmooth RegularizedGraphNorm
open ContinuousSourceCoordinates PhysicalMomentProjection NormalizedCubicRemainder
open ContinuousResolventBounds NonlinearRegularizedStep GraphResolventSmooth

theorem actual_uniform_implicit_radius {R : ℝ} (hR : 0<R) {K : Set Parameter}
    (hK : IsCompact K) (hpos : K⊆positiveDomain R) :
    ∃κ : ℝ,0<κ ∧ ∀θ,(hθ : θ∈K) → ∀(s : ℝ)(hs : 1 ≤ s),
      ∀(F : X R)(q : graphSpace hR.le s),‖read q‖<κ →
      step hR (hpos hθ) hs F q=q →
      ∃g : Parameter×X R → graphSpace hR.le s,
        ContDiffAt ℝ ∞ g (θ,F) ∧ g (θ,F)=q ∧
        ∀ᶠ a in 𝓝 (θ,F),jointStep hR s (a,g a)=g a := by
  obtain ⟨A,hA,hlin⟩ := actual_graph_resolvent_bound hR hK hpos
  obtain ⟨B,hB,hrem⟩ := actual_compact_remainder_oneY hR hK hpos
  let κ : ℝ := min 1 (1/(4*A*B))
  have hκ : 0<κ := lt_min zero_lt_one (by positivity)
  have hκ1 : κ≤1 := min_le_left _ _
  have hsmall : A*B*κ≤(1/4:ℝ) := by
    calc
      _≤A*B*(1/(4*A*B)) := mul_le_mul_of_nonneg_left (min_le_right _ _) (by positivity)
      _=_ := by field_simp [hA.ne',hB.ne']
  refine ⟨κ,hκ,?_⟩
  intro θ hθ s hs F q hq hfix
  letI : CompleteSpace (graphSpace hR.le s) := graph_complete hR.le s
  have hn : ∀ᶠ r : graphSpace hR.le s in 𝓝 q,‖read r‖<κ :=
    ((readMap hR.le s).continuous.norm.isOpen_preimage (Iio κ) isOpen_Iio).eventually_mem hq
  have hlip : ∀ᶠ r : graphSpace hR.le s in 𝓝 q,
      ‖jointStep hR s ((θ,F),r)-jointStep hR s ((θ,F),q)‖≤(1/4:ℝ)*‖r-q‖ := by
    filter_upwards [hn] with r hr
    rw [jointStep_eq hR (hpos hθ) hs,jointStep_eq hR (hpos hθ) hs]
    exact (step_difference_bound hR (hpos hθ) hs hA.le hB.le hκ.le
      (hlin θ hθ s hs) F r q
      (hrem θ hθ κ hκ1 (read r) (read q) hr.le hq.le)).trans
        (mul_le_mul_of_nonneg_right hsmall (norm_nonneg _))
  exact @SmoothContractionImplicit.actual_local_smooth_fixed_point
    (Parameter×X R) (graphSpace hR.le s) inferInstance inferInstance inferInstance
    inferInstance inferInstance (graph_complete hR.le s)
    (jointStep hR s) (θ,F) q
    (jointStep_contDiffAt hR (hpos hθ) (zero_lt_one.trans_le hs) F q)
    (by rw [jointStep_eq hR (hpos hθ) hs]; exact hfix) (1/4) (by norm_num) (by norm_num) hlip

theorem actual_local_smooth_original_cell {R : ℝ} (hR : 0<R) {K : Set Parameter}
    (hK : IsCompact K) (hpos : K⊆positiveDomain R) :
    ∃κ : ℝ,0<κ ∧ ∀θ,(hθ : θ∈K) → ∀(s : ℝ)(_hs : 1 ≤ s),∀F q : X R,
      ‖q‖<κ → projection hR (hpos hθ) (sourceMap hR F)=0 →
      q-s • (denominatorMap R θ*FiberContinuity.collisionMap R hR.le
        (profileMap R θ*(1+q)))=F →
      ∃g : Parameter×X R → X R,ContDiffAt ℝ ∞ g (θ,F) ∧ g (θ,F)=q ∧
        ∀ᶠ a in 𝓝 (θ,F),a.1∈positiveDomain R ∧
          ∀ha : a.1∈positiveDomain R,projection hR ha (sourceMap hR a.2)=0 →
            g a-s • (denominatorMap R a.1*FiberContinuity.collisionMap R hR.le
              (profileMap R a.1*(1+g a)))=a.2 ∧
            projection hR ha (sourceMap hR (g a))=0 := by
  obtain ⟨κ,hκ,himp⟩ := actual_uniform_implicit_radius hR hK hpos
  refine ⟨κ,hκ,?_⟩
  intro θ hθ s hs F q hq hF he
  have hfix := NonlinearCellUniqueness.actual_solution_fixed_point hR (hpos hθ) hs q F hF he
  obtain ⟨g,hg,hgq,hge⟩ := himp θ hθ s hs F (lift hR.le s q) hq hfix
  refine ⟨fun a=>readMap hR.le s (g a),(readMap hR.le s).contDiff.contDiffAt.comp (θ,F) hg,
    by change readMap hR.le s (g (θ,F))=q; rw [hgq]; rfl,?_⟩
  have hn : ∀ᶠ a : Parameter×X R in 𝓝 (θ,F),a.1∈positiveDomain R :=
    ((positiveDomain_isOpen R).preimage continuous_fst).eventually_mem (hpos hθ)
  filter_upwards [hge,hn] with a hga ha
  refine ⟨ha,?_⟩
  intro ha' hFa
  rw [jointStep_eq hR ha' hs] at hga
  exact fixed_point_original_equation hR ha' hs a.2 (g a) hFa hga

theorem actual_exists_smooth_nonlinear_cell {R : ℝ} (hR : 0<R) {K : Set Parameter}
    (hK : IsCompact K) (hpos : K⊆positiveDomain R) :
    ∃δ C : ℝ,0<δ ∧ 0<C ∧ ∀θ,(hθ : θ∈K) → ∀(s : ℝ)(_hs : 1 ≤ s),∀F : X R,
      ‖F‖≤δ → projection hR (hpos hθ) (sourceMap hR F)=0 →
      ∃q : X R,
        q-s • (denominatorMap R θ*FiberContinuity.collisionMap R hR.le (profileMap R θ*(1+q)))=F ∧
        projection hR (hpos hθ) (sourceMap hR q)=0 ∧
        ‖q‖≤C*‖F‖ ∧ s*‖OneWeightedPairReadout.referenceContinuous hR.le*q‖≤C*‖F‖ ∧
        ∃g : Parameter×X R → X R,ContDiffAt ℝ ∞ g (θ,F) ∧ g (θ,F)=q ∧
          ∀ᶠ a in 𝓝 (θ,F),a.1∈positiveDomain R ∧
            ∀ha : a.1∈positiveDomain R,projection hR ha (sourceMap hR a.2)=0 →
              g a-s • (denominatorMap R a.1*FiberContinuity.collisionMap R hR.le
                (profileMap R a.1*(1+g a)))=a.2 ∧
              projection hR ha (sourceMap hR (g a))=0 := by
  obtain ⟨δ,C,hδ,hC,hex⟩ := NonlinearRegularizedCell.actual_nonlinear_regularized_cell hR hK hpos
  obtain ⟨κ,hκ,hsmooth⟩ := actual_local_smooth_original_cell hR hK hpos
  refine ⟨min δ (κ/(2*C)),C,lt_min hδ (by positivity),hC,?_⟩
  intro θ hθ s hs F hFn hF
  obtain ⟨q,he,hm,hq,hw,_⟩ := hex θ hθ s hs F (hFn.trans (min_le_left _ _)) hF
  have hqκ : ‖q‖<κ := by
    have hb : ‖q‖≤κ/2 := hq.trans ((mul_le_mul_of_nonneg_left
      (hFn.trans (min_le_right _ _)) hC.le).trans_eq (by field_simp [hC.ne']))
    exact hb.trans_lt (by linarith)
  exact ⟨q,he,hm,hq,hw,hsmooth θ hθ s hs F q hqκ hF he⟩

end
end Resonance.NonlinearCellSmooth
