import Resonance.PinnedWeakOutputL1
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Basic

/-! A setwise Radon--Nikodym identity is promoted to every bounded measurable
test by actual simple-function approximation and dominated convergence. -/
open Set MeasureTheory Filter
open scoped Topology
namespace Resonance.RNTestFunctions
noncomputable section
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

theorem simple_test (μ : Measure X) (ν : Measure Y) {T : X→Y} (hT : Measurable T)
    {f : X→ℂ} {g : Y→ℂ} (hf : Integrable f μ) (hg : Integrable g ν)
    (he : ∀s,MeasurableSet s→(∫y in s,g y ∂ν)=∫x in T⁻¹' s,f x ∂μ)
    (S : SimpleFunc Y ℂ) :
    Integrable (fun y=>S y*g y) ν ∧ Integrable (fun x=>S (T x)*f x) μ ∧
      (∫y,S y*g y ∂ν)=∫x,S (T x)*f x ∂μ := by
  induction S using SimpleFunc.induction with
  | @const c s hs =>
    have eL : (fun y=>SimpleFunc.piecewise s hs (SimpleFunc.const Y c)
        (SimpleFunc.const Y 0) y*g y)=s.indicator (fun y=>c*g y) := by
      funext y
      by_cases hy:y∈s
      · simp [SimpleFunc.piecewise,hy]
      · simp [SimpleFunc.piecewise,hy]
    have eR : (fun x=>SimpleFunc.piecewise s hs (SimpleFunc.const Y c)
        (SimpleFunc.const Y 0) (T x)*f x)=(T⁻¹' s).indicator (fun x=>c*f x) := by
      funext x
      by_cases hx:T x∈s
      · simp [SimpleFunc.piecewise,hx]
      · simp [SimpleFunc.piecewise,hx]
    rw [eL,eR]
    refine ⟨(hg.const_mul c).indicator hs,(hf.const_mul c).indicator (hT hs),?_⟩
    rw [integral_indicator hs,integral_indicator (hT hs)]
    exact (integral_const_mul c g).trans
      ((congrArg (fun z:ℂ=>c*z) (he s hs)).trans (integral_const_mul c f).symm)
  | @add S U _ hS hU =>
    have eL : (fun y=>(S+U) y*g y)=(fun y=>S y*g y)+(fun y=>U y*g y) := by
      ext y; simp [add_mul]
    have eR : (fun x=>(S+U) (T x)*f x)=(fun x=>S (T x)*f x)+(fun x=>U (T x)*f x) := by
      ext x; simp [add_mul]
    rw [eL,eR]
    refine ⟨hS.1.add hU.1,hS.2.1.add hU.2.1,?_⟩
    exact (integral_add hS.1 hU.1).trans
      ((congrArg₂ (fun x y:ℂ=>x+y) hS.2.2 hU.2.2).trans
        (integral_add hS.2.1 hU.2.1).symm)

theorem bounded_test (μ : Measure X) (ν : Measure Y) {T : X→Y} (hT : Measurable T)
    {f : X→ℂ} {g : Y→ℂ} (hf : Integrable f μ) (hg : Integrable g ν)
    (he : ∀s,MeasurableSet s→(∫y in s,g y ∂ν)=∫x in T⁻¹' s,f x ∂μ)
    {ψ : Y→ℂ} (hψ : Measurable ψ) {C : ℝ} (hC : 0≤C) (hbound : ∀y,‖ψ y‖≤C) :
    Integrable (fun y=>ψ y*g y) ν ∧ Integrable (fun x=>ψ (T x)*f x) μ ∧
      (∫y,ψ y*g y ∂ν)=∫x,ψ (T x)*f x ∂μ := by
  have hsm : StronglyMeasurable ψ := hψ.stronglyMeasurable
  let S := hsm.approxBounded C
  have hS := fun n=>simple_test μ ν hT hf hg he (S n)
  have hSb : ∀n y,‖S n y‖≤C := hsm.norm_approxBounded_le hC
  have hSt : ∀y,Tendsto (fun n=>S n y) atTop (𝓝 (ψ y)) :=
    fun y=>hsm.tendsto_approxBounded_of_norm_le (hbound y)
  have hiL : Integrable (fun y=>ψ y*g y) ν := by
    apply (hg.norm.const_mul C).mono' (hψ.aestronglyMeasurable.mul hg.aestronglyMeasurable)
    exact Eventually.of_forall (fun y=>by
      change ‖ψ y*g y‖≤C*‖g y‖
      rw [norm_mul]; exact mul_le_mul_of_nonneg_right (hbound y) (norm_nonneg _))
  have hiR : Integrable (fun x=>ψ (T x)*f x) μ := by
    apply (hf.norm.const_mul C).mono' ((hψ.comp hT).aestronglyMeasurable.mul hf.aestronglyMeasurable)
    exact Eventually.of_forall (fun x=>by
      change ‖ψ (T x)*f x‖≤C*‖f x‖
      rw [norm_mul]; exact mul_le_mul_of_nonneg_right (hbound (T x)) (norm_nonneg _))
  have htL := tendsto_integral_of_dominated_convergence (fun y=>C*‖g y‖)
    (fun n=>(hS n).1.aestronglyMeasurable) (hg.norm.const_mul C)
    (fun n=>Eventually.of_forall (fun y=>by
      rw [norm_mul]; exact mul_le_mul_of_nonneg_right (hSb n y) (norm_nonneg _)))
    (Eventually.of_forall (fun y=>(hSt y).mul tendsto_const_nhds))
  have htR := tendsto_integral_of_dominated_convergence (fun x=>C*‖f x‖)
    (fun n=>(hS n).2.1.aestronglyMeasurable) (hf.norm.const_mul C)
    (fun n=>Eventually.of_forall (fun x=>by
      rw [norm_mul]; exact mul_le_mul_of_nonneg_right (hSb n (T x)) (norm_nonneg _)))
    (Eventually.of_forall (fun x=>(hSt (T x)).mul tendsto_const_nhds))
  exact ⟨hiL,hiR,tendsto_nhds_unique htL
    (htR.congr' (Eventually.of_forall (fun n=>(hS n).2.2.symm)))⟩

end
end Resonance.RNTestFunctions
