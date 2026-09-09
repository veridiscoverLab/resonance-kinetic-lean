import Resonance.L2RectangleDensity
import Resonance.L2KernelPairing
import Mathlib.Analysis.Normed.Operator.Compact

/-! Compactness is derived from the actual L² kernel and the literal complete
bilinear integral identity. No positivity, symmetry or compactness is assumed. -/
open MeasureTheory Set
open scoped ENNReal InnerProductSpace Topology
namespace Resonance.HilbertSchmidtCompact
noncomputable section
open Resonance.L2KernelPairing Resonance.L2RectangleDensity
variable {X Y:Type*} [MeasurableSpace X] [MeasurableSpace Y]
variable (μ:Measure X) (ν:Measure Y) [IsFiniteMeasure μ] [IsFiniteMeasure ν]

def rankOne (a:Lp ℝ 2 μ) (b:Lp ℝ 2 ν) : Lp ℝ 2 ν→L[ℝ]Lp ℝ 2 μ :=
  (innerSL ℝ b).smulRight a

omit [IsFiniteMeasure μ] [IsFiniteMeasure ν] in
theorem rankOne_compact (a:Lp ℝ 2 μ) (b:Lp ℝ 2 ν) : IsCompactOperator (rankOne μ ν a b) := by
  have h := isCompactOperator_of_locallyCompactSpace_dom (innerSL ℝ b)
  exact h.continuous_comp (continuous_id.smul continuous_const)

theorem rankOne_represents (a:Lp ℝ 2 μ) (b:Lp ℝ 2 ν) :
    Represents μ ν (tensor μ ν b a) (rankOne μ ν a b) := by
  rw [represents_iff_inner]
  intro u v
  change inner ℝ v ((inner ℝ b u)•a)=_
  rw [real_inner_smul_right,tensor_inner,real_inner_comm a v,mul_comm]

theorem rectangle_eq_tensor (s:Set X) (t:Set Y) (hs:MeasurableSet s) (ht:MeasurableSet t) :
    indicatorConstLp 2 (hs.prod ht) (measure_ne_top _ _) (1:ℝ)
      =tensor μ ν (indicatorConstLp 2 ht (measure_ne_top _ _) (1:ℝ))
        (indicatorConstLp 2 hs (measure_ne_top _ _) (1:ℝ)) := by
  apply Lp.ext
  have ha := (Measure.quasiMeasurePreserving_fst (μ:=μ) (ν:=ν)).ae
    (indicatorConstLp_coeFn (p:=2) (hs:=hs) (hμs:=measure_ne_top _ _) (c:=(1:ℝ)))
  have hb := (Measure.quasiMeasurePreserving_snd (μ:=μ) (ν:=ν)).ae
    (indicatorConstLp_coeFn (p:=2) (hs:=ht) (hμs:=measure_ne_top _ _) (c:=(1:ℝ)))
  filter_upwards [indicatorConstLp_coeFn (p:=2) (hs:=hs.prod ht)
    (hμs:=measure_ne_top _ _) (c:=(1:ℝ)),ha,hb,tensor_coe μ ν
      (indicatorConstLp 2 ht (measure_ne_top _ _) (1:ℝ))
      (indicatorConstLp 2 hs (measure_ne_top _ _) (1:ℝ))] with p hp hpa hpb hpt
  rw [hp,hpt,hpa,hpb]
  by_cases hx:p.1∈s <;> by_cases hy:p.2∈t <;> simp [hx,hy]

theorem span_has_compact_representation {K:Lp ℝ 2 (μ.prod ν)} (hK:K∈rectangleSpan μ ν) :
    ∃S:Lp ℝ 2 ν→L[ℝ]Lp ℝ 2 μ,IsCompactOperator S ∧ Represents μ ν K S := by
  induction hK using Submodule.span_induction with
  | mem K hK =>
      rcases hK with ⟨s,t,hs,ht,rfl⟩
      rw [rectangle_eq_tensor μ ν s t hs ht]
      exact ⟨_,rankOne_compact μ ν _ _,rankOne_represents μ ν _ _⟩
  | zero => exact ⟨0,isCompactOperator_zero,represents_zero μ ν⟩
  | add K L _ _ hK hL =>
      obtain ⟨T,hTc,hT⟩ := hK
      obtain ⟨S,hSc,hS⟩ := hL
      exact ⟨T+S,hTc.add hSc,hT.add μ ν hS⟩
  | smul c K _ hK =>
      obtain ⟨T,hTc,hT⟩ := hK
      exact ⟨c•T,hTc.smul c,hT.smul μ ν c⟩

theorem isCompactOperator_of_L2_kernel {K:Lp ℝ 2 (μ.prod ν)}
    {T:Lp ℝ 2 ν→L[ℝ]Lp ℝ 2 μ} (hT:Represents μ ν K T) : IsCompactOperator T := by
  apply isClosed_setOf_isCompactOperator.closure_subset
  rw [Metric.mem_closure_iff]
  intro ε hε
  obtain ⟨L,hL,hKL⟩ := Metric.mem_closure_iff.mp (rectangleSpan_dense μ ν K) ε hε
  obtain ⟨S,hSc,hS⟩ := span_has_compact_representation μ ν hL
  refine ⟨S,hSc,?_⟩
  rw [dist_eq_norm] at hKL ⊢
  exact (represents_norm_bound μ ν (hT.sub μ ν hS)).trans_lt hKL

theorem isCompactOperator_of_memLp_kernel {K:X×Y→ℝ} (hK:MemLp K 2 (μ.prod ν))
    {T:Lp ℝ 2 ν→L[ℝ]Lp ℝ 2 μ}
    (hT:∀u v,inner ℝ v (T u)=∫p,K p*u p.2*v p.1 ∂(μ.prod ν)) : IsCompactOperator T := by
  apply isCompactOperator_of_L2_kernel μ ν (K:=hK.toLp K)
  intro u v
  rw [hT]
  apply integral_congr_ae
  filter_upwards [hK.coeFn_toLp] with p hp
  simp only [hp]

end
end Resonance.HilbertSchmidtCompact
