import Resonance.CollisionPositivity
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Calculus.ContDiff.Basic

/-! The full cubic collision is the diagonal of a bounded, actual-fiber
trilinear operator.  No differentiability assumption on the collision is used. -/
open MeasureTheory Set Metric Function
open scoped ENNReal NNReal BigOperators ContDiff
namespace Resonance.CollisionMultilinear
noncomputable section
set_option maxHeartbeats 900000
open Resonance.PlaneCoarea Resonance.CollisionFiber Resonance.FiberContinuity
open Resonance.CollisionPositivity

abbrev CubeFunction (R : ℝ) := C(ResonantMeasure.cube R,ℝ)

/-- Linear zero extension at a fixed momentum; continuity is not asserted off the cube. -/
def zeroEval (R : ℝ) (k : E) : CubeFunction R →L[ℝ] ℝ := by
  classical
  exact if hk : k∈ResonantMeasure.cube R then ContinuousMap.evalCLM ℝ ⟨k,hk⟩ else 0

theorem zeroEval_inside (R : ℝ) (f : CubeFunction R) {k : E}
    (hk : k∈ResonantMeasure.cube R) : zeroEval R k f=f ⟨k,hk⟩ := by
  simp [zeroEval,hk]

theorem zeroEval_norm_le (R : ℝ) (f : CubeFunction R) (k : E) :
    ‖zeroEval R k f‖≤‖f‖ := by
  by_cases hk : k∈ResonantMeasure.cube R
  · rw [zeroEval_inside R f hk]
    exact f.norm_coe_le_norm _
  · simp [zeroEval,hk]

theorem zeroEval_eq_indicator (R : ℝ) (f : CubeFunction R) :
    (fun k => zeroEval R k f) =
      (ResonantMeasure.cube R).indicator (continuousExtension R f) := by
  funext k
  by_cases hk : k∈ResonantMeasure.cube R
  · rw [zeroEval_inside R f hk,Set.indicator_of_mem hk,continuousExtension_eq R f ⟨k,hk⟩]
  · simp [zeroEval,hk]

theorem zeroEval_measurable (R : ℝ) (f : CubeFunction R) :
    Measurable (fun k => zeroEval R k f) := by
  rw [zeroEval_eq_indicator]
  exact (continuousExtension R f).continuous.measurable.indicator
    (ResonantMeasure.measurable_cube R)

def pointParent (R : ℝ) (legs : Fin 3 → Fin 4) (q : FourMomenta) :
    MultilinearMap ℝ (fun _ : Fin 3 => CubeFunction R) ℝ :=
  (MultilinearMap.mkPiAlgebra ℝ (Fin 3) ℝ).compLinearMap
    (fun j => (zeroEval R (q (legs j))).toLinearMap)

theorem pointParent_apply (R : ℝ) (legs : Fin 3 → Fin 4)
    (q : FourMomenta) (m : Fin 3 → CubeFunction R) :
    pointParent R legs q m=∏ j,zeroEval R (q (legs j)) (m j) := rfl

theorem pointParent_measurable (R : ℝ) (legs : Fin 3 → Fin 4)
    (m : Fin 3 → CubeFunction R) : Measurable (fun q => pointParent R legs q m) := by
  simp_rw [pointParent_apply]
  apply Finset.measurable_prod
  intro j _
  exact (zeroEval_measurable R (m j)).comp (measurable_pi_apply (legs j))

theorem pointParent_bound (R : ℝ) (legs : Fin 3 → Fin 4)
    (q : FourMomenta) (m : Fin 3 → CubeFunction R) :
    ‖pointParent R legs q m‖≤∏ j,‖m j‖ := by
  rw [pointParent_apply,norm_prod]
  exact Finset.prod_le_prod (fun _ _ => norm_nonneg _)
    (fun j _ => zeroEval_norm_le R (m j) (q (legs j)))

theorem pointParent_integrable {R : ℝ} (hR : 0≤R) (legs : Fin 3 → Fin 4)
    (m : Fin 3 → CubeFunction R) (k : E) :
    Integrable (fun q => pointParent R legs q m) (fiberMeasure R k) :=
  fiber_integrable_of_bounded hR _ (pointParent_measurable R legs m)
    (fun q _ => pointParent_bound R legs q m) k

theorem pointParent_extension (R : ℝ) (legs : Fin 3 → Fin 4)
    (m : Fin 3 → CubeFunction R) {q : FourMomenta}
    (hq : q∈CoareaNormalization.allFourFlags R) :
    pointParent R legs q m=∏ j,continuousExtension R (m j) (q (legs j)) := by
  rw [pointParent_apply]
  apply Finset.prod_congr rfl
  intro j _
  rw [zeroEval_inside R (m j) (hq (legs j)),
    continuousExtension_eq R (m j) ⟨q (legs j),hq (legs j)⟩]

theorem parentIntegral_continuousOn {R : ℝ} (hR : 0≤R) (legs : Fin 3 → Fin 4)
    (m : Fin 3 → CubeFunction R) :
    ContinuousOn (fun k => ∫ q,pointParent R legs q m ∂fiberMeasure R k)
      (ResonantMeasure.cube R) := by
  let Φ := fun q : FourMomenta => ∏ j,continuousExtension R (m j) (q (legs j))
  have heq : (fun k => ∫ q,pointParent R legs q m ∂fiberMeasure R k)=fiberReadout R Φ := by
    funext k
    apply integral_congr_ae
    filter_upwards [fiber_support R k] with q hq
    exact pointParent_extension R legs m hq.1
  rw [heq]
  apply fiberReadout_continuousOn hR Φ
  unfold Φ
  fun_prop

def parentOutput (R : ℝ) (hR : 0≤R) (legs : Fin 3 → Fin 4)
    (m : Fin 3 → CubeFunction R) : CubeFunction R :=
  ⟨fun k => ∫ q,pointParent R legs q m ∂fiberMeasure R k,
    continuousOn_iff_continuous_restrict.mp (parentIntegral_continuousOn hR legs m)⟩

def parentMultilinear (R : ℝ) (hR : 0≤R) (legs : Fin 3 → Fin 4) :
    MultilinearMap ℝ (fun _ : Fin 3 => CubeFunction R) (CubeFunction R) where
  toFun := parentOutput R hR legs
  map_update_add' := by
    intro _ m i f g
    ext k
    change (∫ q,pointParent R legs q (update m i (f+g)) ∂fiberMeasure R k)=
      (∫ q,pointParent R legs q (update m i f) ∂fiberMeasure R k)+
      (∫ q,pointParent R legs q (update m i g) ∂fiberMeasure R k)
    simp_rw [MultilinearMap.map_update_add]
    exact integral_add (pointParent_integrable hR legs _ k) (pointParent_integrable hR legs _ k)
  map_update_smul' := by
    intro _ m i c f
    ext k
    change (∫ q,pointParent R legs q (update m i (c • f)) ∂fiberMeasure R k)=
      c • (∫ q,pointParent R legs q (update m i f) ∂fiberMeasure R k)
    simp_rw [MultilinearMap.map_update_smul]
    exact integral_smul c _

theorem parentMultilinear_bound {R : ℝ} (hR : 0≤R) (legs : Fin 3 → Fin 4)
    (m : Fin 3 → CubeFunction R) :
    ‖parentMultilinear R hR legs m‖≤(fiberMassBound R).toReal * ∏ j,‖m j‖ := by
  apply (ContinuousMap.norm_le _ (by positivity)).mpr
  intro k
  letI := collisionKernel_finite hR
  haveI : IsFiniteMeasure (fiberMeasure R k) :=
    inferInstanceAs (IsFiniteMeasure (collisionKernel R k))
  change ‖∫ q,pointParent R legs q m ∂fiberMeasure R k‖≤_
  have hi := norm_integral_le_of_norm_le_const
    (ae_of_all (fiberMeasure R k) (fun q => pointParent_bound R legs q m))
  have hm := ENNReal.toReal_mono (fiberMassBound_lt_top R).ne (fiberMeasure_mass_le hR k)
  calc
    _ ≤ (∏ j,‖m j‖)*(fiberMeasure R k univ).toReal := hi
    _ ≤ (∏ j,‖m j‖)*(fiberMassBound R).toReal :=
      mul_le_mul_of_nonneg_left hm (by positivity)
    _ = _ := mul_comm _ _

def parentContinuous (R : ℝ) (hR : 0≤R) (legs : Fin 3 → Fin 4) :
    ContinuousMultilinearMap ℝ (fun _ : Fin 3 => CubeFunction R) (CubeFunction R) :=
  (parentMultilinear R hR legs).mkContinuous (fiberMassBound R).toReal
    (parentMultilinear_bound hR legs)

/-- One operator includes every original cubic parent, with its original sign. -/
def collisionTrilinear (R : ℝ) (hR : 0≤R) :
    ContinuousMultilinearMap ℝ (fun _ : Fin 3 => CubeFunction R) (CubeFunction R) :=
  parentContinuous R hR ![1,2,3]+parentContinuous R hR ![0,2,3]-
    parentContinuous R hR ![0,1,3]-parentContinuous R hR ![0,1,2]

theorem parentContinuous_norm_le {R : ℝ} (hR : 0≤R) (legs : Fin 3 → Fin 4) :
    ‖parentContinuous R hR legs‖≤(fiberMassBound R).toReal :=
  MultilinearMap.mkContinuous_norm_le _ ENNReal.toReal_nonneg _

theorem collisionTrilinear_norm_le {R : ℝ} (hR : 0≤R) :
    ‖collisionTrilinear R hR‖≤4*(fiberMassBound R).toReal := by
  unfold collisionTrilinear
  have h1 := norm_add_le (parentContinuous R hR ![1,2,3]) (parentContinuous R hR ![0,2,3])
  have h2 := norm_sub_le (parentContinuous R hR ![1,2,3]+parentContinuous R hR ![0,2,3])
    (parentContinuous R hR ![0,1,3])
  have h3 := norm_sub_le (parentContinuous R hR ![1,2,3]+parentContinuous R hR ![0,2,3]-
    parentContinuous R hR ![0,1,3]) (parentContinuous R hR ![0,1,2])
  linarith [parentContinuous_norm_le hR ![1,2,3],parentContinuous_norm_le hR ![0,2,3],
    parentContinuous_norm_le hR ![0,1,3],parentContinuous_norm_le hR ![0,1,2]]

theorem collisionTrilinear_integral {R : ℝ} (hR : 0≤R)
    (m : Fin 3 → CubeFunction R) (k : ResonantMeasure.cube R) :
    collisionTrilinear R hR m k = ∫ q,
      pointParent R ![1,2,3] q m+pointParent R ![0,2,3] q m-
      pointParent R ![0,1,3] q m-pointParent R ![0,1,2] q m ∂fiberMeasure R k := by
  have h1 := pointParent_integrable hR ![1,2,3] m (k:E)
  have h2 := pointParent_integrable hR ![0,2,3] m (k:E)
  have h3 := pointParent_integrable hR ![0,1,3] m (k:E)
  have h4 := pointParent_integrable hR ![0,1,2] m (k:E)
  have h12 : Integrable (fun q => pointParent R ![1,2,3] q m+
      pointParent R ![0,2,3] q m) (fiberMeasure R k) := h1.add h2
  have h123 : Integrable (fun q => pointParent R ![1,2,3] q m+
      pointParent R ![0,2,3] q m-pointParent R ![0,1,3] q m) (fiberMeasure R k) := h12.sub h3
  rw [integral_sub h123 h4,integral_sub h12 h3,integral_add h1 h2]
  rfl

/-- The diagonal is exactly the frozen original collision map, not a new polynomial model. -/
theorem collisionTrilinear_diagonal {R : ℝ} (hR : 0≤R) (f : CubeFunction R) :
    collisionTrilinear R hR (fun _ => f)=collisionMap R hR f := by
  ext k
  rw [collisionTrilinear_integral,collisionMap_apply R hR _ (fun p => zeroEval R p f)
    (fun p => zeroEval_inside R f p.property)]
  apply integral_congr_ae
  apply ae_of_all
  intro q
  simp only [pointParent_apply,Fin.prod_univ_succ,Fin.prod_univ_zero,mul_one,
    Matrix.cons_val_zero,Matrix.cons_val_succ,collisionIntegrand,Collision.collisionPolynomial]
  ring

def diagonal (R : ℝ) : CubeFunction R →L[ℝ] (Fin 3 → CubeFunction R) :=
  ContinuousLinearMap.pi (fun _ => ContinuousLinearMap.id ℝ (CubeFunction R))

theorem diagonal_apply (R : ℝ) (f : CubeFunction R) : diagonal R f=(fun _ => f) := rfl

theorem collisionMap_eq_diagonal {R : ℝ} (hR : 0≤R) :
    collisionMap R hR = (collisionTrilinear R hR) ∘ (diagonal R) :=
  funext (fun f => (collisionTrilinear_diagonal hR f).symm)

/-- All Fréchet smoothness orders follow from the actually constructed multilinear operator. -/
theorem collisionMap_contDiff {R : ℝ} (hR : 0≤R) (n : WithTop ℕ∞) :
    ContDiff ℝ n (collisionMap R hR) := by
  rw [collisionMap_eq_diagonal hR]
  exact (collisionTrilinear R hR).contDiff.comp (diagonal R).contDiff

theorem collisionMap_hasFDerivAt {R : ℝ} (hR : 0≤R) (f : CubeFunction R) :
    HasFDerivAt (collisionMap R hR)
      (((collisionTrilinear R hR).linearDeriv (fun _ => f)).comp (diagonal R)) f := by
  rw [collisionMap_eq_diagonal hR]
  exact ((collisionTrilinear R hR).hasFDerivAt (diagonal R f)).comp f (diagonal R).hasFDerivAt

theorem collisionMap_hasStrictFDerivAt {R : ℝ} (hR : 0≤R) (f : CubeFunction R) :
    HasStrictFDerivAt (collisionMap R hR)
      (((collisionTrilinear R hR).linearDeriv (fun _ => f)).comp (diagonal R)) f := by
  rw [collisionMap_eq_diagonal hR]
  exact ((collisionTrilinear R hR).hasStrictFDerivAt (diagonal R f)).comp f
    (diagonal R).hasStrictFDerivAt

theorem collisionMap_fderiv_apply {R : ℝ} (hR : 0≤R) (f h : CubeFunction R) :
    fderiv ℝ (collisionMap R hR) f h =
      ∑ i : Fin 3,collisionTrilinear R hR (update (fun _ => f) i h) := by
  rw [(collisionMap_hasFDerivAt hR f).fderiv]
  simp [ContinuousLinearMap.comp_apply,ContinuousMultilinearMap.linearDeriv_apply,diagonal_apply]

/-- Every derivative retains every injection of the direction slots into the three cubic slots. -/
def derivativeCoefficient (R : ℝ) (hR : 0≤R) (n : ℕ) (f : CubeFunction R) :
    ContinuousMultilinearMap ℝ (fun _ : Fin n => CubeFunction R) (CubeFunction R) :=
  ((collisionTrilinear R hR).iteratedFDeriv n (fun _ => f)).compContinuousLinearMap
    (fun _ => diagonal R)

theorem collisionMap_iteratedFDeriv {R : ℝ} (hR : 0≤R) (n : ℕ) (f : CubeFunction R) :
    iteratedFDeriv ℝ n (collisionMap R hR) f=derivativeCoefficient R hR n f := by
  rw [collisionMap_eq_diagonal hR,
    (diagonal R).iteratedFDeriv_comp_right ((collisionTrilinear R hR).contDiff (n := ⊤)) f (by simp),
    (collisionTrilinear R hR).iteratedFDeriv_eq]
  rfl

theorem derivativeCoefficient_apply {R : ℝ} (hR : 0≤R) (n : ℕ)
    (f : CubeFunction R) (v : Fin n → CubeFunction R) :
    derivativeCoefficient R hR n f v = ∑ e : Fin n ↪ Fin 3,
      collisionTrilinear R hR (fun j =>
        if hj : j∈Set.range e then v (e.toEquivRange.symm ⟨j,hj⟩) else f) := by
  classical
  simp [derivativeCoefficient,ContinuousMultilinearMap.iteratedFDeriv,
    ContinuousMultilinearMap.iteratedFDerivComponent_apply,diagonal_apply]
  apply Finset.sum_congr rfl
  intro e _
  congr 1
  funext j
  split_ifs with hj
  · obtain ⟨i,rfl⟩ := hj
    simp only [Function.Embedding.toEquivRange_symm_apply_self]
  · rfl

theorem collisionMap_second_derivative {R : ℝ} (hR : 0≤R) (f : CubeFunction R) :
    iteratedFDeriv ℝ 2 (collisionMap R hR) f=derivativeCoefficient R hR 2 f :=
  collisionMap_iteratedFDeriv hR 2 f

theorem collisionMap_third_derivative {R : ℝ} (hR : 0≤R) (f : CubeFunction R) :
    iteratedFDeriv ℝ 3 (collisionMap R hR) f=derivativeCoefficient R hR 3 f :=
  collisionMap_iteratedFDeriv hR 3 f

theorem collisionMap_third_derivative_constant {R : ℝ} (hR : 0≤R)
    (f g : CubeFunction R) :
    iteratedFDeriv ℝ 3 (collisionMap R hR) f=iteratedFDeriv ℝ 3 (collisionMap R hR) g := by
  classical
  simp only [collisionMap_iteratedFDeriv]
  apply ContinuousMultilinearMap.ext
  intro v
  rw [derivativeCoefficient_apply,derivativeCoefficient_apply]
  apply Finset.sum_congr rfl
  intro e _
  congr 1
  funext j
  have hj : j∈Set.range e := (Finite.surjective_of_injective e.injective) j
  simp only [dif_pos hj]

/-- There are no injections of four or more direction slots into three cubic slots. -/
theorem collisionMap_higher_derivatives_zero {R : ℝ} (hR : 0≤R)
    {n : ℕ} (hn : 4≤n) (f : CubeFunction R) :
    iteratedFDeriv ℝ n (collisionMap R hR) f=0 := by
  classical
  haveI : IsEmpty (Fin n ↪ Fin 3) := ⟨fun e => by
    have hc := Fintype.card_le_of_injective e e.injective
    simp only [Fintype.card_fin] at hc
    omega⟩
  rw [collisionMap_iteratedFDeriv]
  ext v
  rw [derivativeCoefficient_apply]
  simp

theorem diagonal_norm_le (R : ℝ) : ‖diagonal R‖≤1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro f
  simp [diagonal_apply]

/-- Uniform operator-norm bounds for every genuine derivative of the original cubic. -/
theorem collisionMap_iteratedFDeriv_norm_le {R : ℝ} (hR : 0≤R)
    (n : ℕ) (f : CubeFunction R) :
    ‖iteratedFDeriv ℝ n (collisionMap R hR) f‖ ≤
      (Nat.descFactorial 3 n : ℝ)*(4*(fiberMassBound R).toReal)*‖f‖^(3-n) := by
  rw [collisionMap_iteratedFDeriv]
  let T := collisionTrilinear R hR
  have hprod : (∏ _ : Fin n, ‖diagonal R‖)≤1 := by
    calc
      _ ≤ ∏ _ : Fin n,(1:ℝ) := Finset.prod_le_prod
        (fun (_ : Fin n) _ => norm_nonneg (diagonal R))
        (fun (_ : Fin n) _ => diagonal_norm_le R)
      _ = 1 := by simp
  have hi : ‖T.iteratedFDeriv n (fun _ => f)‖ ≤
      (Nat.descFactorial 3 n : ℝ)*‖T‖*‖f‖^(3-n) := by
    simpa using T.norm_iteratedFDeriv_le' n (fun _ => f)
  calc
    _ ≤ ‖T.iteratedFDeriv n (fun _ => f)‖*(∏ _ : Fin n,‖diagonal R‖) :=
      ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _
    _ ≤ ‖T.iteratedFDeriv n (fun _ => f)‖ := by nlinarith [norm_nonneg (T.iteratedFDeriv n (fun _ => f))]
    _ ≤ (Nat.descFactorial 3 n : ℝ)*‖T‖*‖f‖^(3-n) := hi
    _ ≤ _ := by
      gcongr
      exact collisionTrilinear_norm_le hR

/-! Complete theorem-type and logical-dependency audit. -/
#check zeroEval_inside
#print axioms zeroEval_inside
#check zeroEval_norm_le
#print axioms zeroEval_norm_le
#check zeroEval_eq_indicator
#print axioms zeroEval_eq_indicator
#check zeroEval_measurable
#print axioms zeroEval_measurable
#check pointParent_apply
#print axioms pointParent_apply
#check pointParent_measurable
#print axioms pointParent_measurable
#check pointParent_bound
#print axioms pointParent_bound
#check pointParent_integrable
#print axioms pointParent_integrable
#check pointParent_extension
#print axioms pointParent_extension
#check parentIntegral_continuousOn
#print axioms parentIntegral_continuousOn
#check parentMultilinear_bound
#print axioms parentMultilinear_bound
#check parentContinuous_norm_le
#print axioms parentContinuous_norm_le
#check collisionTrilinear_norm_le
#print axioms collisionTrilinear_norm_le
#check collisionTrilinear_integral
#print axioms collisionTrilinear_integral
#check collisionTrilinear_diagonal
#print axioms collisionTrilinear_diagonal
#check diagonal_apply
#print axioms diagonal_apply
#check collisionMap_eq_diagonal
#print axioms collisionMap_eq_diagonal
#check collisionMap_contDiff
#print axioms collisionMap_contDiff
#check collisionMap_hasFDerivAt
#print axioms collisionMap_hasFDerivAt
#check collisionMap_hasStrictFDerivAt
#print axioms collisionMap_hasStrictFDerivAt
#check collisionMap_fderiv_apply
#print axioms collisionMap_fderiv_apply
#check collisionMap_iteratedFDeriv
#print axioms collisionMap_iteratedFDeriv
#check derivativeCoefficient_apply
#print axioms derivativeCoefficient_apply
#check collisionMap_second_derivative
#print axioms collisionMap_second_derivative
#check collisionMap_third_derivative
#print axioms collisionMap_third_derivative
#check collisionMap_third_derivative_constant
#print axioms collisionMap_third_derivative_constant
#check collisionMap_higher_derivatives_zero
#print axioms collisionMap_higher_derivatives_zero
#check diagonal_norm_le
#print axioms diagonal_norm_le
#check collisionMap_iteratedFDeriv_norm_le
#print axioms collisionMap_iteratedFDeriv_norm_le

end
end Resonance.CollisionMultilinear
