import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.AEEqOfIntegral
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule

/-! Rectangular indicator kernels span a dense subspace of the actual product L².
The proof uses the product sigma algebra, not a kernel-compactness hypothesis. -/
open MeasureTheory Set
open scoped ENNReal InnerProductSpace
namespace Resonance.L2RectangleDensity
noncomputable section
variable {X Y:Type*} [MeasurableSpace X] [MeasurableSpace Y]
variable (μ:Measure X) (ν:Measure Y) [IsFiniteMeasure μ] [IsFiniteMeasure ν]

def rectangleVectors : Set (Lp ℝ 2 (μ.prod ν)) :=
  {f | ∃(s:Set X)(t:Set Y)(hs:MeasurableSet s)(ht:MeasurableSet t),
    f=indicatorConstLp 2 (hs.prod ht) (measure_ne_top _ _) (1:ℝ)}

def rectangleSpan : Submodule ℝ (Lp ℝ 2 (μ.prod ν)) :=
  Submodule.span ℝ (rectangleVectors μ ν)

theorem integrable_zero_of_rectangle_integrals {f:X×Y→ℝ}
    (hf:Integrable f (μ.prod ν))
    (hrect:∀(s:Set X)(t:Set Y),MeasurableSet s→MeasurableSet t→
      ∫p in s×ˢt,f p ∂(μ.prod ν)=0) : f=ᵐ[μ.prod ν]0 := by
  apply hf.ae_eq_zero_of_forall_setIntegral_eq_zero
  intro s hs _
  have huniv : ∫p,f p ∂(μ.prod ν)=0 := by
    simpa using hrect univ univ MeasurableSet.univ MeasurableSet.univ
  induction s,hs using MeasurableSpace.induction_on_inter
      generateFrom_prod.symm isPiSystem_prod with
  | empty => simp
  | basic s hs =>
      rcases hs with ⟨s,hs,t,ht,rfl⟩
      exact hrect s t hs ht
  | compl s hs ih => rw [setIntegral_compl hs hf, huniv, ih (measure_lt_top _ _), sub_self]
  | iUnion f hd hm ih => rw [integral_iUnion hm hd hf.integrableOn]; simp [ih]

theorem rectangleSpan_orthogonal_eq_bot : (rectangleSpan μ ν)ᗮ=⊥ := by
  apply le_antisymm
  · intro f hf
    have hfi : Integrable f (μ.prod ν) := (Lp.memLp f).integrable (by norm_num)
    have hzero : f=ᵐ[μ.prod ν]0 := integrable_zero_of_rectangle_integrals μ ν hfi (by
      intro s t hs ht
      have hm : indicatorConstLp 2 (hs.prod ht) (measure_ne_top _ _) (1:ℝ)
          ∈rectangleSpan μ ν := Submodule.subset_span ⟨s,t,hs,ht,rfl⟩
      have hh := (Submodule.mem_orthogonal _ _).mp hf _ hm
      rw [L2.inner_indicatorConstLp_eq_setIntegral_inner] at hh
      convert hh using 1
      congr 1
      ext p
      change f p=f p*1
      ring)
    have he : f=0 := Lp.ext (hzero.trans (Lp.coeFn_zero (E:=ℝ) (p:=2) (μ:=μ.prod ν)).symm)
    simp [he]
  · exact bot_le

theorem rectangleSpan_dense : Dense (rectangleSpan μ ν:Set (Lp ℝ 2 (μ.prod ν))) := by
  have h := (rectangleSpan μ ν).orthogonal_orthogonal_eq_closure
  rw [rectangleSpan_orthogonal_eq_bot,Submodule.bot_orthogonal_eq_top] at h
  have he : (rectangleSpan μ ν).topologicalClosure=⊤ := h.symm
  exact Submodule.dense_iff_topologicalClosure_eq_top.mpr he

end
end Resonance.L2RectangleDensity
