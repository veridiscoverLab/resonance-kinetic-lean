import Resonance.L2Evaluation
import Resonance.L2BoundedExponential

/-! A genuine Bochner identity and forward derivative in the complete,
common coefficient space. The spatial smoothing W and its composition
with the original generator have separately proved uniform bounds. -/
open Set MeasureTheory
open scoped NNReal
namespace Resonance.L2SmoothedEvolution
noncomputable section
open L2DiagonalOperator L2Evaluation L2BoundedExponential HilbertExponentialFlow
variable {I E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable (G W : I→E→L[ℂ]E) {C A B : ℝ}
variable (hC : 0≤C) (hG : ∀t : ℝ≥0,∀i,‖flow (G i) t‖≤C)
variable (hA : 0≤A) (hW : ∀i,‖W i‖≤A)
variable (hB : 0≤B) (hWG : ∀i,‖W i*G i‖≤B)

def path (v : Space I E) (t : ℝ) : Space I E :=
  semigroup G hC hG (Real.toNNReal t) v

theorem path_continuous (v : Space I E) : Continuous (path G hC hG v) :=
  (semigroup_strong_continuous G hC hG v).comp continuous_real_toNNReal

omit [CompleteSpace E] in
theorem path_apply (v : Space I E) {t : ℝ} (ht : 0≤t) (i : I) :
    path G hC hG v t i=flow (G i) t (v i) := by
  simp only [path,semigroup_apply,Real.coe_toNNReal t ht]

set_option backward.isDefEq.respectTransparency false in
theorem complete_integral_identity (v : Space I E) {t : ℝ} (ht : 0≤t) :
    diagonal W hA hW (path G hC hG v t)=diagonal W hA hW v+
      ∫s in 0..t,diagonal (fun i=>W i*G i) hB hWG (path G hC hG v s) := by
  let D:=diagonal (fun i=>W i*G i) hB hWG
  have hc : Continuous (fun s=>D (path G hC hG v s)) :=
    D.continuous.comp (path_continuous G hC hG v)
  apply Subtype.ext
  funext i
  change W i (path G hC hG v t i)=W i (v i)+(∫s in 0..t,D (path G hC hG v s)) i
  rw [evaluation_intervalIntegral i (hc.intervalIntegrable 0 t)]
  have hi : (∫s in 0..t,D (path G hC hG v s) i)=
      W i (flow (G i) t (v i))-W i (v i) := by
    trans ∫s in 0..t,W i (G i (flow (G i) s (v i)))
    · apply intervalIntegral.integral_congr
      intro s hs
      have hs0 : 0≤s := (uIcc_of_le ht ▸ hs).1
      change W i (G i (path G hC hG v s i))=_
      rw [path_apply G hC hG v hs0]
    · have hd : ∀s,HasDerivAt (fun s=>W i (flow (G i) s (v i)))
          (W i (G i (flow (G i) s (v i)))) s := fun s=>
          ((W i).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt s
            (flow_hasDerivAt (G i) (v i) s)
      have hf : Continuous (fun s=>W i (G i (flow (G i) s (v i)))) :=
        (W i).continuous.comp ((G i).continuous.comp
          (continuous_iff_continuousAt.mpr (fun s=>(flow_hasDerivAt (G i) (v i) s).continuousAt)))
      simpa only [flow_zero,ContinuousLinearMap.one_apply] using
        intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _=>hd s)
          (hf.intervalIntegrable 0 t)
  rw [hi,path_apply G hC hG v ht]
  abel

set_option backward.isDefEq.respectTransparency false in
theorem complete_forward_derivative (v : Space I E) {t : ℝ} (ht : 0≤t) :
    HasDerivWithinAt (fun s=>diagonal W hA hW (path G hC hG v s))
      (diagonal (fun i=>W i*G i) hB hWG (path G hC hG v t)) (Ici 0) t := by
  let D:=diagonal (fun i=>W i*G i) hB hWG
  have hc : Continuous (fun s=>D (path G hC hG v s)) :=
    D.continuous.comp (path_continuous G hC hG v)
  have hd := (intervalIntegral.integral_hasDerivAt_right
    (hc.intervalIntegrable 0 t)
    hc.aestronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt).const_add
      (diagonal W hA hW v)
  exact hd.hasDerivWithinAt.congr_of_mem
    (fun s hs=>complete_integral_identity G W hC hG hA hW hB hWG v hs) ht

end
end Resonance.L2SmoothedEvolution
