import Resonance.CollisionRotations
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Calculus.MeanValue

/-! Classification for differentiable representatives, derived from the
original full pairing measure. The measurable-to-smooth bridge is separate. -/
open Set MeasureTheory
open scoped RealInnerProductSpace

namespace Resonance.QuadraticCollisionInvariants
noncomputable section
open ResonantMeasure ContinuousCollisionInvariants ParallelGradientAlgebra CollisionRotations

theorem openCube_convex (R : ℝ) : Convex ℝ (openCube R) := by
  have he : openCube R = ⋂ j : Fin 3, (PiLp.projₗ (𝕜 := ℝ) 2 (fun _ : Fin 3 => ℝ) j) ⁻¹' Ioo (-R) R := by
    ext x
    simp [openCube, abs_lt]
  rw [he]
  exact convex_iInter (fun j => (convex_Ioo (-R) R).linear_preimage _)

theorem zero_mem_openCube {R : ℝ} (hR : 0 < R) : (0 : E) ∈ openCube R := by
  intro j
  simpa using hR

theorem half_axis_mem_openCube {R : ℝ} (hR : 0 < R) (j : Fin 3) :
    axisPoint (R/2) j ∈ openCube R := by
  intro i
  by_cases hij : i=j
  · simp only [axisPoint_apply, if_pos hij, abs_of_pos (half_pos hR)]
    linarith
  · simpa only [axisPoint_apply, if_neg hij, abs_zero] using hR

theorem coordinate_gradient_affine {R : ℝ} (hR : 0 < R) {f : E → ℝ}
    (hfd : ∀ x∈openCube R, DifferentiableAt ℝ f x) (hf : invariant R f) :
    ∃ c : ℝ, ∀ x∈openCube R, ∀ i,
      fderiv ℝ f x (axisPoint 1 i) = fderiv ℝ f 0 (axisPoint 1 i) + c*x i := by
  exact affine_of_parallel_increments (openCube R) (coordinateGradient f)
    (zero_mem_openCube hR) (R/2) (ne_of_gt (half_pos hR))
    (half_axis_mem_openCube hR) (coordinateGradient_parallel hfd hf)

theorem vector_axis_expansion (v : E) : v = ∑ i : Fin 3, v i • axisPoint 1 i := by
  ext j
  simp [axisPoint, Fin.sum_univ_succ]
  fin_cases j <;> simp

theorem continuousLinearMap_eq_of_axis {A B : E →L[ℝ] ℝ}
    (h : ∀ i, A (axisPoint 1 i) = B (axisPoint 1 i)) : A = B := by
  ext v
  rw [vector_axis_expansion v]
  simp only [map_sum, map_smul, smul_eq_mul, h]

theorem inner_axis (x : E) (i : Fin 3) : inner ℝ x (axisPoint 1 i) = x i := by
  have he : axisPoint 1 i = EuclideanSpace.single i (1 : ℝ) := by
    ext j
    simp [axisPoint, PiLp.single_apply, eq_comm]
  rw [he]
  simpa using (EuclideanSpace.inner_single_right (𝕜 := ℝ) i 1 x)

theorem derivative_affine {R : ℝ} (hR : 0 < R) {f : E → ℝ}
    (hfd : ∀ x∈openCube R, DifferentiableAt ℝ f x) (hf : invariant R f) :
    ∃ c : ℝ, ∀ x∈openCube R, fderiv ℝ f x = fderiv ℝ f 0 + c • innerSL ℝ x := by
  obtain ⟨c,hc⟩ := coordinate_gradient_affine hR hfd hf
  refine ⟨c,fun x hx => continuousLinearMap_eq_of_axis (fun i => ?_)⟩
  simpa only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    innerSL_apply_apply, smul_eq_mul, inner_axis] using hc x hx i

def quadratic (a : ℝ) (b : E →L[ℝ] ℝ) (c : ℝ) (x : E) : ℝ :=
  a+b x+(c/2)*‖x‖^2

theorem quadratic_hasFDerivAt (a : ℝ) (b : E →L[ℝ] ℝ) (c : ℝ) (x : E) :
    HasFDerivAt (quadratic a b c) (b+c • innerSL ℝ x) x := by
  have h := (b.hasFDerivAt.const_add a).add
    ((hasStrictFDerivAt_norm_sq x).hasFDerivAt.const_mul (c/2))
  convert h using 1
  ext v
  simp
  ring

theorem differentiable_collision_invariant_quadratic {R : ℝ} (hR : 0 < R) {f : E → ℝ}
    (hfd : ∀ x∈openCube R, DifferentiableAt ℝ f x) (hf : invariant R f) :
    ∃ c : ℝ, ∀ x∈openCube R, f x = f 0 + fderiv ℝ f 0 x + (c/2)*‖x‖^2 := by
  obtain ⟨c,hc⟩ := derivative_affine hR hfd hf
  refine ⟨c,?_⟩
  have hq (x : E) := quadratic_hasFDerivAt (f 0) (fderiv ℝ f 0) c x
  have he : EqOn f (quadratic (f 0) (fderiv ℝ f 0) c) (openCube R) := by
    apply (openCube_convex R).eqOn_of_fderivWithin_eq
      (fun x hx => (hfd x hx).differentiableWithinAt)
      (fun x _ => (hq x).differentiableAt.differentiableWithinAt)
      (openCube_isOpen R).uniqueDiffOn
    · intro x hx
      rw [fderivWithin_of_isOpen (openCube_isOpen R) hx,
        fderivWithin_of_isOpen (openCube_isOpen R) hx, (hq x).fderiv, hc x hx]
    · exact zero_mem_openCube hR
    · simp [quadratic]
  exact he

end
end Resonance.QuadraticCollisionInvariants
