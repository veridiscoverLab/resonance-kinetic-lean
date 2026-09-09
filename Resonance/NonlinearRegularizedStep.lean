import Resonance.ContinuousResolventBounds
import Resonance.NormalizedRemainderMoments

/-! The same original nonlinear regularized equation as a map on its
complete two-norm graph space. The source moment condition is proved for
every nonlinear iterate from the full collision conservation law. -/
open Set
namespace Resonance.NonlinearRegularizedStep
noncomputable section
set_option maxHeartbeats 2000000
open ResonantMeasure Thermodynamics ProfileBanachSmooth
open NormalizedCubicRemainder NormalizedRemainderMoments OneWeightedPairReadout
open ContinuousRegularizedEquation ContinuousResolventBounds ContinuousSourceCoordinates
open RegularizedGraphNorm PhysicalMomentProjection

def step {R : ℝ} (hR : 0<R) {θ : Parameter} (hθ : θ∈positiveDomain R)
    {s : ℝ} (hs : 1 ≤ s) (F : X R) (q : graphSpace hR.le s) : graphSpace hR.le s :=
  lift hR.le s (output hR hθ (zero_lt_one.trans_le hs)
    (F+s • remainder R hR.le θ (read q)))

theorem step_source_micro {R : ℝ} (hR : 0<R) {θ : Parameter} (hθ : θ∈positiveDomain R)
    {s : ℝ} (_hs : 1 ≤ s) (F : X R) (q : graphSpace hR.le s)
    (hF : projection hR hθ (sourceMap hR F)=0) :
    projection hR hθ (sourceMap hR (F+s • remainder R hR.le θ (read q)))=0 := by
  rw [map_add,map_smul,map_add,map_smul,hF,
    show projection hR hθ (sourceMap hR (remainder R hR.le θ (read q)))=0 from
      actual_remainder_source_micro hR hθ (read q),smul_zero,add_zero]

theorem step_micro {R : ℝ} (hR : 0<R) {θ : Parameter} (hθ : θ∈positiveDomain R)
    {s : ℝ} (hs : 1 ≤ s) (F : X R) (q : graphSpace hR.le s)
    (hF : projection hR hθ (sourceMap hR F)=0) :
    projection hR hθ (sourceMap hR (read (step hR hθ hs F q)))=0 :=
  output_micro hR hθ (zero_lt_one.trans_le hs) _ (step_source_micro hR hθ hs F q hF)

theorem step_zero {R : ℝ} (hR : 0<R) {θ : Parameter} (hθ : θ∈positiveDomain R)
    {s : ℝ} (hs : 1 ≤ s) (F : X R) :
    step hR hθ hs F 0=lift hR.le s (output hR hθ (zero_lt_one.trans_le hs) F) := by
  unfold step
  change lift hR.le s (output hR hθ _ (F+s • remainder R hR.le θ 0))=_
  rw [remainder_zero,smul_zero,add_zero]

theorem step_difference_bound {R : ℝ} (hR : 0<R) {θ : Parameter}
    (hθ : θ∈positiveDomain R) {s : ℝ} (hs : 1 ≤ s) {A C κ : ℝ}
    (hA : 0≤A) (hC : 0≤C) (hκ : 0≤κ)
    (hlin : ∀G : X R,‖lift hR.le s (output hR hθ (zero_lt_one.trans_le hs) G)‖≤A*‖G‖)
    (F : X R) (q r : graphSpace hR.le s)
    (hrem : ‖remainder R hR.le θ (read q)-remainder R hR.le θ (read r)‖≤
      C*κ*‖referenceContinuous hR.le*(read q-read r)‖) :
    ‖step hR hθ hs F q-step hR hθ hs F r‖≤(A*C*κ)*‖q-r‖ := by
  have hs0 : 0<s := zero_lt_one.trans_le hs
  have hsrc : (F+s • remainder R hR.le θ (read q))-
      (F+s • remainder R hR.le θ (read r))=
        s • (remainder R hR.le θ (read q)-remainder R hR.le θ (read r)) := by
    simp only [smul_sub]
    abel
  unfold step
  rw [←lift_sub,←output_sub,hsrc]
  calc
    _≤A*‖s • (remainder R hR.le θ (read q)-remainder R hR.le θ (read r))‖ := hlin _
    _=A*(s*‖remainder R hR.le θ (read q)-remainder R hR.le θ (read r)‖) := by
      rw [norm_smul,Real.norm_of_nonneg hs0.le]
    _≤A*(s*(C*κ*‖referenceContinuous hR.le*(read q-read r)‖)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hrem hs0.le) hA
    _=(A*C*κ)*(s*‖referenceContinuous hR.le*read (q-r)‖) := by rw [read_sub]; ring
    _≤(A*C*κ)*‖q-r‖ := mul_le_mul_of_nonneg_left (weighted_norm_le hs0.le (q-r)) (by positivity)

theorem fixed_point_original_equation {R : ℝ} (hR : 0<R) {θ : Parameter}
    (hθ : θ∈positiveDomain R) {s : ℝ} (hs : 1 ≤ s) (F : X R) (q : graphSpace hR.le s)
    (hF : projection hR hθ (sourceMap hR F)=0) (hq : step hR hθ hs F q=q) :
    read q-s • (denominatorMap R θ*FiberContinuity.collisionMap R hR.le
      (profileMap R θ*(1+read q)))=F ∧
      projection hR hθ (sourceMap hR (read q))=0 := by
  have hread := congrArg read hq
  change output hR hθ (zero_lt_one.trans_le hs) (F+s • remainder R hR.le θ (read q))=read q at hread
  have he := actual_continuous_regularized_equation hR hθ (zero_lt_one.trans_le hs)
    (F+s • remainder R hR.le θ (read q)) (step_source_micro hR hθ hs F q hF)
  rw [hread] at he
  refine ⟨?_,?_⟩
  · rw [actual_normalized_decomposition hR.le hθ,smul_add,←sub_sub,he,add_sub_cancel_right]
  · have hm := step_micro hR hθ hs F q hF
    rwa [hq] at hm

end
end Resonance.NonlinearRegularizedStep
