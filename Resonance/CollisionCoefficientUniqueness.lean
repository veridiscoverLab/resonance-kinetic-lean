import Resonance.QuadraticPointwiseClosure

/-! The coefficients on overlapping physical cubes are forced to agree. -/
open Set MeasureTheory Filter
open scoped Topology RealInnerProductSpace

namespace Resonance.CollisionCoefficientUniqueness
noncomputable section
open ResonantMeasure ContinuousCollisionInvariants ParallelGradientAlgebra
open QuadraticCollisionInvariants QuadraticPointwiseClosure

theorem evaluate_continuous (a : Coefficients) : Continuous (evaluate a) := by
  unfold evaluate
  fun_prop

theorem evaluate_hasFDerivAt (a : Coefficients) (x : E) :
    HasFDerivAt (evaluate a) (a.2.1+(2*a.2.2) • innerSL ℝ x) x := by
  have h := (a.2.1.hasFDerivAt.const_add a.1).add
    ((hasStrictFDerivAt_norm_sq x).hasFDerivAt.const_mul a.2.2)
  convert h using 1
  ext v
  simp
  ring

theorem evaluate_hasFDerivAt_zero (a : Coefficients) :
    HasFDerivAt (evaluate a) a.2.1 0 := by
  have he : a.2.1+(2*a.2.2) • innerSL ℝ (0 : E)=a.2.1 := by
    ext v
    simp only [ContinuousLinearMap.add_apply,ContinuousLinearMap.smul_apply,
      innerSL_apply_apply,inner_zero_left,smul_eq_mul,mul_zero,add_zero]
  rw [← he]
  exact evaluate_hasFDerivAt a 0

theorem coefficients_eq_of_eqOn {R : ℝ} (hR : 0 < R) {a b : Coefficients}
    (hab : EqOn (evaluate a) (evaluate b) (openCube R)) : a=b := by
  have h0 := hab (zero_mem_openCube hR)
  have ha : a.1=b.1 := by simpa [evaluate] using h0
  have he : evaluate a =ᶠ[𝓝 0] evaluate b :=
    Filter.mem_of_superset ((openCube_isOpen R).mem_nhds (zero_mem_openCube hR)) hab
  have hb : a.2.1=b.2.1 :=
    ((evaluate_hasFDerivAt_zero a).congr_of_eventuallyEq he.symm).unique
      (evaluate_hasFDerivAt_zero b)
  let x := axisPoint (R/2) 0
  have hx : x≠0 := by
    intro h
    have hi := congrArg (fun y : E => y 0) h
    have hz : R/2=0 := by simpa [x,axisPoint] using hi
    linarith
  have hp := hab (half_axis_mem_openCube hR 0)
  change a.1+a.2.1 x+a.2.2*‖x‖^2=b.1+b.2.1 x+b.2.2*‖x‖^2 at hp
  rw [ha,hb] at hp
  have hc : a.2.2=b.2.2 := by
    have hn := sq_pos_of_pos (norm_pos_iff.mpr hx)
    nlinarith
  exact Prod.ext ha (Prod.ext hb hc)

theorem coefficients_eq_of_ae {R : ℝ} (hR : 0 < R) {a b : Coefficients}
    (hab : evaluate a =ᵐ[(volume : Measure E).restrict (openCube R)] evaluate b) : a=b := by
  exact coefficients_eq_of_eqOn hR (Measure.eqOn_open_of_ae_eq hab (openCube_isOpen R)
    (evaluate_continuous a).continuousOn (evaluate_continuous b).continuousOn)

end
end Resonance.CollisionCoefficientUniqueness
