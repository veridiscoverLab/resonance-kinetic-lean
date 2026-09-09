import Resonance.CollisionMultilinear
import Resonance.SpatialCollision
import Mathlib.Analysis.Calculus.ContDiff.Comp

/-! The actual spatial collision inherits its multilinear structure from the
same four-leg fiber at each common spatial point.  Spatial differentiability
below concerns the real lift of the torus; no momentum derivative is used. -/
open Set Function
open scoped BigOperators ContDiff
namespace Resonance.SpatialCollisionJets
noncomputable section
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000
open FreeTransport SpatialCollision CollisionFiber

def sectionCLM (R : ℝ) (x : SpatialTorus) :
    Distribution R →L[ℝ] CollisionMultilinear.CubeFunction R :=
  LinearMap.mkContinuous
    { toFun := fun f => momentumSection f x
      map_add' := by intros; ext k; rfl
      map_smul' := by intros; ext k; rfl }
    1 (fun f => by simpa using momentumSection_norm_le f x)

theorem sectionCLM_apply (R : ℝ) (x : SpatialTorus) (f : Distribution R) :
    sectionCLM R x f=momentumSection f x := rfl

theorem sectionCLM_norm_le (R : ℝ) (x : SpatialTorus) : ‖sectionCLM R x‖≤1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro f
  simpa using momentumSection_norm_le f x

def trilinearOutput (R : ℝ) (hR : 0≤R) (m : Fin 3 → Distribution R) :
    Distribution R :=
  ContinuousMap.uncurry
    ⟨fun x => CollisionMultilinear.collisionTrilinear R hR
      (fun j => momentumSection (m j) x),
      ((CollisionMultilinear.collisionTrilinear R hR).contDiff (n := ⊤)).continuous.comp
        (continuous_pi (fun j => (m j).curry.continuous))⟩

theorem trilinearOutput_apply (R : ℝ) (hR : 0≤R) (m : Fin 3 → Distribution R)
    (x : SpatialTorus) (k : MomentumDomain R) :
    trilinearOutput R hR m (x,k)=
      CollisionMultilinear.collisionTrilinear R hR (fun j => momentumSection (m j) x) k := rfl

def spatialMultilinear (R : ℝ) (hR : 0≤R) :
    MultilinearMap ℝ (fun _ : Fin 3 => Distribution R) (Distribution R) where
  toFun := trilinearOutput R hR
  map_update_add' := by
    intro _ m i f g
    ext p
    change CollisionMultilinear.collisionTrilinear R hR
        (fun j => sectionCLM R p.1 (update m i (f+g) j)) p.2 =
      CollisionMultilinear.collisionTrilinear R hR
        (fun j => sectionCLM R p.1 (update m i f j)) p.2 +
      CollisionMultilinear.collisionTrilinear R hR
        (fun j => sectionCLM R p.1 (update m i g j)) p.2
    let ht := (CollisionMultilinear.collisionTrilinear R hR).compContinuousLinearMap
      (fun _ : Fin 3 => sectionCLM R p.1)
    exact congrArg (fun z : CollisionMultilinear.CubeFunction R => z p.2)
      (ht.map_update_add m i f g)
  map_update_smul' := by
    intro _ m i c f
    ext p
    let ht := (CollisionMultilinear.collisionTrilinear R hR).compContinuousLinearMap
      (fun _ : Fin 3 => sectionCLM R p.1)
    exact congrArg (fun z : CollisionMultilinear.CubeFunction R => z p.2)
      (ht.map_update_smul m i c f)

theorem spatialMultilinear_bound {R : ℝ} (hR : 0≤R) (m : Fin 3 → Distribution R) :
    ‖spatialMultilinear R hR m‖≤4*(fiberMassBound R).toReal*∏ j,‖m j‖ := by
  apply (ContinuousMap.norm_le _ (by positivity)).mpr
  intro p
  change ‖CollisionMultilinear.collisionTrilinear R hR
      (fun j => momentumSection (m j) p.1) p.2‖≤_
  calc
    _ ≤ ‖CollisionMultilinear.collisionTrilinear R hR
        (fun j => momentumSection (m j) p.1)‖ :=
      (CollisionMultilinear.collisionTrilinear R hR _).norm_coe_le_norm p.2
    _ ≤ ‖CollisionMultilinear.collisionTrilinear R hR‖ *
        ∏ j,‖momentumSection (m j) p.1‖ :=
      (CollisionMultilinear.collisionTrilinear R hR).le_opNorm _
    _ ≤ _ := mul_le_mul (CollisionMultilinear.collisionTrilinear_norm_le hR)
      (Finset.prod_le_prod (fun _ _ => norm_nonneg _)
        (fun j _ => momentumSection_norm_le (m j) p.1))
      (by positivity) (by positivity)

def spatialTrilinear (R : ℝ) (hR : 0≤R) :
    ContinuousMultilinearMap ℝ (fun _ : Fin 3 => Distribution R) (Distribution R) :=
  (spatialMultilinear R hR).mkContinuous (4*(fiberMassBound R).toReal)
    (spatialMultilinear_bound hR)

theorem spatialTrilinear_norm_le {R : ℝ} (hR : 0≤R) :
    ‖spatialTrilinear R hR‖≤4*(fiberMassBound R).toReal :=
  MultilinearMap.mkContinuous_norm_le _ (by positivity) _

theorem spatialTrilinear_apply {R : ℝ} (hR : 0≤R) (m : Fin 3 → Distribution R)
    (x : SpatialTorus) (k : MomentumDomain R) :
    spatialTrilinear R hR m (x,k)=
      CollisionMultilinear.collisionTrilinear R hR (fun j => momentumSection (m j) x) k := rfl

theorem spatialTrilinear_original_integral {R : ℝ} (hR : 0≤R)
    (m : Fin 3 → Distribution R) (x : SpatialTorus) (k : MomentumDomain R) :
    spatialTrilinear R hR m (x,k)=∫ q,
      CollisionMultilinear.pointParent R ![1,2,3] q (fun j => momentumSection (m j) x)+
      CollisionMultilinear.pointParent R ![0,2,3] q (fun j => momentumSection (m j) x)-
      CollisionMultilinear.pointParent R ![0,1,3] q (fun j => momentumSection (m j) x)-
      CollisionMultilinear.pointParent R ![0,1,2] q (fun j => momentumSection (m j) x)
        ∂fiberMeasure R k := by
  exact CollisionMultilinear.collisionTrilinear_integral hR _ k

theorem spatialTrilinear_diagonal {R : ℝ} (hR : 0≤R) (f : Distribution R) :
    spatialTrilinear R hR (fun _ => f)=collision R hR f := by
  ext p
  change CollisionMultilinear.collisionTrilinear R hR
    (fun _ => momentumSection f p.1) p.2=FiberContinuity.collisionMap R hR
      (momentumSection f p.1) p.2
  rw [CollisionMultilinear.collisionTrilinear_diagonal hR]

def diagonal (R : ℝ) : Distribution R →L[ℝ] (Fin 3 → Distribution R) :=
  ContinuousLinearMap.pi (fun _ => ContinuousLinearMap.id ℝ (Distribution R))

theorem diagonal_apply (R : ℝ) (f : Distribution R) : diagonal R f=(fun _ => f) := rfl

theorem collision_eq_diagonal {R : ℝ} (hR : 0≤R) :
    collision R hR = (spatialTrilinear R hR) ∘ (diagonal R) :=
  funext (fun f => (spatialTrilinear_diagonal hR f).symm)

theorem collision_contDiff {R : ℝ} (hR : 0≤R) (n : WithTop ℕ∞) :
    ContDiff ℝ n (collision R hR) := by
  rw [collision_eq_diagonal hR]
  exact (spatialTrilinear R hR).contDiff.comp (diagonal R).contDiff

theorem collision_hasFDerivAt {R : ℝ} (hR : 0≤R) (f : Distribution R) :
    HasFDerivAt (collision R hR)
      (((spatialTrilinear R hR).linearDeriv (fun _ => f)).comp (diagonal R)) f := by
  rw [collision_eq_diagonal hR]
  exact ((spatialTrilinear R hR).hasFDerivAt (diagonal R f)).comp f (diagonal R).hasFDerivAt

theorem collision_hasStrictFDerivAt {R : ℝ} (hR : 0≤R) (f : Distribution R) :
    HasStrictFDerivAt (collision R hR)
      (((spatialTrilinear R hR).linearDeriv (fun _ => f)).comp (diagonal R)) f := by
  rw [collision_eq_diagonal hR]
  exact ((spatialTrilinear R hR).hasStrictFDerivAt (diagonal R f)).comp f
    (diagonal R).hasStrictFDerivAt

theorem collision_fderiv_apply {R : ℝ} (hR : 0≤R) (f h : Distribution R) :
    fderiv ℝ (collision R hR) f h =
      ∑ i : Fin 3,spatialTrilinear R hR (update (fun _ => f) i h) := by
  rw [(collision_hasFDerivAt hR f).fderiv]
  simp [ContinuousLinearMap.comp_apply,ContinuousMultilinearMap.linearDeriv_apply,diagonal_apply]

def derivativeCoefficient (R : ℝ) (hR : 0≤R) (n : ℕ) (f : Distribution R) :
    ContinuousMultilinearMap ℝ (fun _ : Fin n => Distribution R) (Distribution R) :=
  ((spatialTrilinear R hR).iteratedFDeriv n (fun _ => f)).compContinuousLinearMap
    (fun _ => diagonal R)

theorem collision_iteratedFDeriv {R : ℝ} (hR : 0≤R) (n : ℕ) (f : Distribution R) :
    iteratedFDeriv ℝ n (collision R hR) f=derivativeCoefficient R hR n f := by
  rw [collision_eq_diagonal hR,
    (diagonal R).iteratedFDeriv_comp_right ((spatialTrilinear R hR).contDiff (n := ⊤)) f (by simp),
    (spatialTrilinear R hR).iteratedFDeriv_eq]
  rfl

theorem derivativeCoefficient_apply {R : ℝ} (hR : 0≤R) (n : ℕ)
    (f : Distribution R) (v : Fin n → Distribution R) :
    derivativeCoefficient R hR n f v = ∑ e : Fin n ↪ Fin 3,
      spatialTrilinear R hR (fun j =>
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

theorem collision_second_derivative {R : ℝ} (hR : 0≤R) (f : Distribution R) :
    iteratedFDeriv ℝ 2 (collision R hR) f=derivativeCoefficient R hR 2 f :=
  collision_iteratedFDeriv hR 2 f

theorem collision_third_derivative {R : ℝ} (hR : 0≤R) (f : Distribution R) :
    iteratedFDeriv ℝ 3 (collision R hR) f=derivativeCoefficient R hR 3 f :=
  collision_iteratedFDeriv hR 3 f

theorem collision_third_derivative_constant {R : ℝ} (hR : 0≤R)
    (f g : Distribution R) :
    iteratedFDeriv ℝ 3 (collision R hR) f=iteratedFDeriv ℝ 3 (collision R hR) g := by
  classical
  simp only [collision_iteratedFDeriv]
  apply ContinuousMultilinearMap.ext
  intro v
  rw [derivativeCoefficient_apply,derivativeCoefficient_apply]
  apply Finset.sum_congr rfl
  intro e _
  congr 1
  funext j
  have hj : j∈Set.range e := (Finite.surjective_of_injective e.injective) j
  simp only [dif_pos hj]

theorem collision_higher_derivatives_zero {R : ℝ} (hR : 0≤R)
    {n : ℕ} (hn : 4≤n) (f : Distribution R) :
    iteratedFDeriv ℝ n (collision R hR) f=0 := by
  classical
  haveI : IsEmpty (Fin n ↪ Fin 3) := ⟨fun e => by
    have hc := Fintype.card_le_of_injective e e.injective
    simp only [Fintype.card_fin] at hc
    omega⟩
  rw [collision_iteratedFDeriv]
  ext v
  rw [derivativeCoefficient_apply]
  simp

theorem diagonal_norm_le (R : ℝ) : ‖diagonal R‖≤1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro f
  simp [diagonal_apply]

theorem collision_iteratedFDeriv_norm_le {R : ℝ} (hR : 0≤R)
    (n : ℕ) (f : Distribution R) :
    ‖iteratedFDeriv ℝ n (collision R hR) f‖ ≤
      (Nat.descFactorial 3 n : ℝ)*(4*(fiberMassBound R).toReal)*‖f‖^(3-n) := by
  rw [collision_iteratedFDeriv]
  let T := spatialTrilinear R hR
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
    _ ≤ _ := by gcongr; exact spatialTrilinear_norm_le hR

#check sectionCLM_apply
#print axioms sectionCLM_apply
#check sectionCLM_norm_le
#print axioms sectionCLM_norm_le
#check trilinearOutput_apply
#print axioms trilinearOutput_apply
#check spatialMultilinear_bound
#print axioms spatialMultilinear_bound
#check spatialTrilinear_norm_le
#print axioms spatialTrilinear_norm_le
#check spatialTrilinear_apply
#print axioms spatialTrilinear_apply
#check spatialTrilinear_original_integral
#print axioms spatialTrilinear_original_integral
#check spatialTrilinear_diagonal
#print axioms spatialTrilinear_diagonal
#check diagonal_apply
#print axioms diagonal_apply
#check collision_eq_diagonal
#print axioms collision_eq_diagonal
#check collision_contDiff
#print axioms collision_contDiff
#check collision_hasFDerivAt
#print axioms collision_hasFDerivAt
#check collision_hasStrictFDerivAt
#print axioms collision_hasStrictFDerivAt
#check collision_fderiv_apply
#print axioms collision_fderiv_apply
#check collision_iteratedFDeriv
#print axioms collision_iteratedFDeriv
#check derivativeCoefficient_apply
#print axioms derivativeCoefficient_apply
#check collision_second_derivative
#print axioms collision_second_derivative
#check collision_third_derivative
#print axioms collision_third_derivative
#check collision_third_derivative_constant
#print axioms collision_third_derivative_constant
#check collision_higher_derivatives_zero
#print axioms collision_higher_derivatives_zero
#check diagonal_norm_le
#print axioms diagonal_norm_le
#check collision_iteratedFDeriv_norm_le
#print axioms collision_iteratedFDeriv_norm_le

end
end Resonance.SpatialCollisionJets
