import Resonance.ContinuousCollisionInvariants
import Resonance.ParallelGradientAlgebra

/-! Tangent identities derived from the original full collision equation.
The same pair is rotated inside the physical cube, preserving momentum and
quadratic energy exactly; no abstract Hessian constraint is postulated. -/
open Set MeasureTheory Filter
open scoped Topology

namespace Resonance.CollisionRotations
noncomputable section
open ResonantMeasure ContinuousCollisionInvariants ParallelGradientAlgebra

def planePart (v : E) (i j : Fin 3) : E := v i • axisPoint 1 i + v j • axisPoint 1 j
def tangent (v : E) (i j : Fin 3) : E := (-v j) • axisPoint 1 i + v i • axisPoint 1 j
def rotate (v : E) (i j : Fin 3) (t : ℝ) : E :=
  v + (Real.cos t-1) • planePart v i j + Real.sin t • tangent v i j

theorem rotate_zero (v : E) (i j : Fin 3) : rotate v i j 0 = v := by
  simp [rotate]

theorem rotate_continuous (v : E) (i j : Fin 3) : Continuous (rotate v i j) := by
  unfold rotate
  fun_prop

theorem rotate_hasDerivAt_zero (v : E) (i j : Fin 3) :
    HasDerivAt (rotate v i j) (tangent v i j) 0 := by
  have h := ((((Real.hasDerivAt_cos 0).sub_const 1).smul_const (planePart v i j)).const_add v).add
    ((Real.hasDerivAt_sin 0).smul_const (tangent v i j))
  simpa only [Real.sin_zero, neg_zero, Real.cos_zero, zero_smul, one_smul, zero_add] using h

theorem rotate_norm (v : E) (i j : Fin 3) (hij : i ≠ j) (t : ℝ) :
    ‖rotate v i j t‖ = ‖v‖ := by
  have he : ‖rotate v i j t‖^2 = ‖v‖^2 := by
    rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq]
    fin_cases i <;> fin_cases j <;> try contradiction
    all_goals simp [rotate, planePart, tangent, axisPoint, Fin.sum_univ_succ]
    all_goals first
      | linear_combination ((v 0)^2+(v 1)^2) * (Real.sin_sq_add_cos_sq t)
      | linear_combination ((v 0)^2+(v 2)^2) * (Real.sin_sq_add_cos_sq t)
      | linear_combination ((v 1)^2+(v 2)^2) * (Real.sin_sq_add_cos_sq t)
  nlinarith [norm_nonneg (rotate v i j t), norm_nonneg v]

theorem collision_tangent_identity {R : ℝ} {f : E → ℝ}
    (hfd : ∀ x∈openCube R, DifferentiableAt ℝ f x) (hf : invariant R f)
    (V v : E) (hv : v ≠ 0) (i j : Fin 3) (hij : i ≠ j)
    (hplus : V+v ∈ openCube R) (hminus : V-v ∈ openCube R) :
    fderiv ℝ f (V+v) (tangent v i j) = fderiv ℝ f (V-v) (tangent v i j) := by
  have hfc : ContinuousOn f (openCube R) := fun x hx => (hfd x hx).continuousAt.continuousWithinAt
  have hpc : Continuous (fun t => V+rotate v i j t) := continuous_const.add (rotate_continuous v i j)
  have hmc : Continuous (fun t => V-rotate v i j t) := continuous_const.sub (rotate_continuous v i j)
  have hp0 : V+rotate v i j 0 ∈ openCube R := by rwa [rotate_zero]
  have hm0 : V-rotate v i j 0 ∈ openCube R := by rwa [rotate_zero]
  have hep := hpc.continuousAt.eventually ((openCube_isOpen R).mem_nhds hp0)
  have hem := hmc.continuousAt.eventually ((openCube_isOpen R).mem_nhds hm0)
  have heq : (fun t => f (V+rotate v i j t)+f (V-rotate v i j t)) =ᶠ[𝓝 0]
      (fun _ => f (V+v)+f (V-v)) := by
    filter_upwards [hep,hem] with t htplus htminus
    exact (continuous_invariant_equal_norm_pair hfc hf V v (rotate v i j t) hv
      (rotate_norm v i j hij t).symm hplus hminus htplus htminus).symm
  have hpd : HasFDerivAt f (fderiv ℝ f (V+v)) (V+rotate v i j 0) := by
    rw [rotate_zero]
    exact (hfd (V+v) hplus).hasFDerivAt
  have hmd : HasFDerivAt f (fderiv ℝ f (V-v)) (V-rotate v i j 0) := by
    rw [rotate_zero]
    exact (hfd (V-v) hminus).hasFDerivAt
  have hp := hpd.comp_hasDerivAt 0
    ((rotate_hasDerivAt_zero v i j).const_add V)
  have hm := hmd.comp_hasDerivAt 0
    ((hasDerivAt_const (0 : ℝ) V).sub (rotate_hasDerivAt_zero v i j))
  have hsum := hp.add hm
  have hz := (hasDerivAt_const (0 : ℝ) (f (V+v)+f (V-v))).congr_of_eventuallyEq heq
  have h := hsum.unique hz
  simpa only [zero_sub, map_neg, ← sub_eq_add_neg, sub_eq_zero] using h

def coordinateGradient (f : E → ℝ) (x : E) : E :=
  WithLp.toLp 2 (fun i => fderiv ℝ f x (axisPoint 1 i))

theorem coordinateGradient_parallel {R : ℝ} {f : E → ℝ}
    (hfd : ∀ x∈openCube R, DifferentiableAt ℝ f x) (hf : invariant R f) :
    parallelIncrements (openCube R) (coordinateGradient f) := by
  intro x hx y hy i j
  by_cases hij : i=j
  · subst j
    rfl
  by_cases hxy : x=y
  · subst y
    simp
  let V : E := (1/2 : ℝ) • (x+y)
  let v : E := (1/2 : ℝ) • (x-y)
  have hp : V+v=x := by dsimp [V,v]; module
  have hm : V-v=y := by dsimp [V,v]; module
  have hv : v ≠ 0 := by
    exact smul_ne_zero (by norm_num : (1/2 : ℝ) ≠ 0) (sub_ne_zero.mpr hxy)
  have h := collision_tangent_identity hfd hf V v hv i j hij (hp.symm ▸ hx) (hm.symm ▸ hy)
  rw [hp,hm] at h
  simp only [tangent, map_add, map_smul, smul_eq_mul] at h
  change (fderiv ℝ f x (axisPoint 1 i)-fderiv ℝ f y (axisPoint 1 i))*(x j-y j) =
    (fderiv ℝ f x (axisPoint 1 j)-fderiv ℝ f y (axisPoint 1 j))*(x i-y i)
  dsimp [v] at h
  linear_combination -2*h

end
end Resonance.CollisionRotations
