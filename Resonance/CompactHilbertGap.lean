import Resonance.HilbertQuadraticBounds
import Mathlib.Topology.MetricSpace.ProperSpace

/-! Compactness turns an exact continuously moving one-dimensional kernel
into a uniform bound on its orthogonal complement. The kernel classification
and positivity are explicit inputs, instantiated by the original matrices. -/
open Set
namespace Resonance.CompactHilbertGap
noncomputable section
set_option maxHeartbeats 800000
open RankTwoHilbert HilbertQuadraticBounds
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E] [ProperSpace E]

omit [ProperSpace E] in
theorem micro_quadratic (T : E→L[ℂ]E) (hT : IsSelfAdjoint T) (e : E)
    (hTe : T e=0) (v : E) : quadratic T (micro e v)=quadratic T v := by
  have he : inner ℂ e (T v)=0 := by
    calc
      _ = inner ℂ (T e) v := (hT.isSymmetric e v).symm
      _ = 0 := by rw [hTe,inner_zero_left]
  simp only [quadratic,micro_apply,map_sub,map_smul,hTe,smul_zero,sub_zero,
    inner_sub_left,inner_smul_left,he,mul_zero,sub_zero]

omit [CompleteSpace E] [ProperSpace E] in
theorem quadratic_smul (T : E→L[ℂ]E) (c : ℂ) (v : E) :
    quadratic T (c • v)=‖c‖^2*quadratic T v := by
  simpa [quadratic] using quadratic_sum_identity T v 0 c

theorem uniform_micro_gap {P : Type*} [TopologicalSpace P] [CompactSpace P]
    (T : P→E→L[ℂ]E) (e : P→E) (hTc : Continuous T) (hec : Continuous e)
    (hTs : ∀p,IsSelfAdjoint (T p)) (he : ∀p,‖e p‖=1)
    (hTe : ∀p,T p (e p)=0)
    (hpos : ∀p v,0 ≤ quadratic (T p) v)
    (hzero : ∀p v,quadratic (T p) v=0 ↔ T p v=0)
    (hkernel : ∀p v,T p v=0 ↔ ∃a : ℂ,v=a • e p) :
    ∃β : ℝ,0 < β ∧ ∀p v,β*‖micro (e p) v‖^2 ≤ quadratic (T p) v := by
  let S : Set (P×E) := ((univ : Set P)×ˢMetric.sphere 0 1) ∩
    {p | inner ℂ (e p.1) p.2=0}
  let V : P×E→ℝ := fun p=>quadratic (T p.1) p.2
  have hc : Continuous V := Complex.continuous_re.comp
    (continuous_snd.inner ((hTc.comp continuous_fst).clm_apply continuous_snd))
  have hs : IsCompact S := (isCompact_univ.prod (isCompact_sphere (0 : E) 1)).inter_right
    (isClosed_eq ((hec.comp continuous_fst).inner continuous_snd) continuous_const)
  have hp : ∀p∈S,0 < V p := by
    intro p hp
    apply lt_of_le_of_ne (hpos p.1 p.2)
    intro hz
    obtain ⟨a,ha⟩ := (hkernel p.1 p.2).mp ((hzero p.1 p.2).mp hz.symm)
    have hao : a=0 := by
      have hh : inner ℂ (e p.1) p.2=0 := hp.2
      rw [ha,inner_smul_right,inner_unit (he p.1),mul_one] at hh
      exact hh
    have hv : p.2=0 := by rw [ha,hao,zero_smul]
    simpa [hv] using hp.1.2
  have hu : ∃β : ℝ,0 < β ∧ ∀p∈S,β ≤ V p := by
    by_cases hn : S.Nonempty
    · obtain ⟨p,hp0,hmin⟩ := hs.exists_isMinOn hn hc.continuousOn
      exact ⟨V p,hp p hp0,fun q hq=>@hmin q hq⟩
    · exact ⟨1,by norm_num,fun p hp=>(hn ⟨p,hp⟩).elim⟩
  obtain ⟨β,hβ,hbound⟩ := hu
  refine ⟨β,hβ,?_⟩
  intro p v
  let q := micro (e p) v
  have hq : inner ℂ (e p) q=0 := micro_orthogonal (he p) v
  rw [←micro_quadratic (T p) (hTs p) (e p) (hTe p) v]
  change β*‖q‖^2 ≤ quadratic (T p) q
  by_cases hz : q=0
  · simp [hz,quadratic]
  have hn : 0 < ‖q‖ := norm_pos_iff.mpr hz
  let w : E := ((‖q‖⁻¹ : ℝ) : ℂ) • q
  have hw : w∈Metric.sphere (0 : E) 1 := by
    simp [w,norm_smul,hn.ne']
  have hwo : inner ℂ (e p) w=0 := by simp only [w,inner_smul_right,hq,mul_zero]
  have hb := hbound (p,w) ⟨⟨mem_univ _,hw⟩,hwo⟩
  have hqw : q=(‖q‖ : ℂ) • w := by
    simp [w,smul_smul,hn.ne']
  have hscale : quadratic (T p) q=‖q‖^2*quadratic (T p) w := by
    conv_lhs => rw [hqw]
    rw [quadratic_smul]
    simp
  rw [hscale]
  change β ≤ quadratic (T p) w at hb
  nlinarith [sq_nonneg ‖q‖]

end
end Resonance.CompactHilbertGap
