import Resonance.CollisionMultilinear
import Resonance.SpatialCollision
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.FDeriv.Symmetric

/-! Explicit third-order composition for the actual torus lift. -/
open Set Function
open scoped BigOperators ContDiff
namespace Resonance.SpatialChainRule
noncomputable section
set_option maxHeartbeats 1500000
set_option synthInstance.maxHeartbeats 200000

theorem sum_partition_succ {A : Type*} [AddCommMonoid A] (n : ℕ)
    (F : OrderedFinpartition (n+1) → A) :
    (∑ c,F c)=∑ c : OrderedFinpartition n,
      (F c.extendLeft+∑ i : Fin c.length,F (c.extendMiddle i)) := by
  classical
  rw [← (OrderedFinpartition.extendEquiv n).sum_comp]
  simp only [Fintype.sum_sigma,OrderedFinpartition.extendEquiv]
  apply Finset.sum_congr rfl
  intro c _
  rw [Fintype.sum_option]
  rfl

abbrev p1 : OrderedFinpartition 1 := (OrderedFinpartition.atomic 0).extendLeft
abbrev p2a : OrderedFinpartition 2 := p1.extendLeft
abbrev p2b : OrderedFinpartition 2 := p1.extendMiddle ⟨0,by change 0<1; omega⟩

theorem sum_partitions_one {A : Type*} [AddCommMonoid A]
    (F : OrderedFinpartition 1 → A) : (∑ c,F c)=F p1 := by
  classical
  rw [sum_partition_succ]
  simp only [Fintype.sum_unique,OrderedFinpartition.default_eq]
  change F p1+(∑ i : Fin 0,F ((OrderedFinpartition.atomic 0).extendMiddle i))=F p1
  simp

theorem sum_partitions_two {A : Type*} [AddCommMonoid A]
    (F : OrderedFinpartition 2 → A) : (∑ c,F c)=F p2a+F p2b := by
  classical
  rw [sum_partition_succ,sum_partitions_one]
  change F p2a+(∑ i : Fin 1,F (p1.extendMiddle i))=F p2a+F p2b
  simp only [Fin.sum_univ_one]
  rfl

theorem sum_partitions_three {A : Type*} [AddCommMonoid A]
    (F : OrderedFinpartition 3 → A) :
    (∑ c,F c)=F p2a.extendLeft+
      F (p2a.extendMiddle ⟨0,by change 0<2; omega⟩)+
      F (p2a.extendMiddle ⟨1,by change 1<2; omega⟩)+
      F p2b.extendLeft+F (p2b.extendMiddle ⟨0,by change 0<1; omega⟩) := by
  classical
  rw [sum_partition_succ,sum_partitions_two]
  change (F p2a.extendLeft+(∑ i : Fin 2,F (p2a.extendMiddle i)))+
    (F p2b.extendLeft+(∑ i : Fin 1,F (p2b.extendMiddle i)))=_
  simp [Fin.sum_univ_two,add_assoc]

section Chain
variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]

theorem taylorComp_three_apply (q : FormalMultilinearSeries ℝ F G)
    (p : FormalMultilinearSeries ℝ E F) (a b c : E) :
    (q.taylorComp p 3) ![a,b,c]=
      q 3 ![p 1 ![a],p 1 ![b],p 1 ![c]]+
      q 2 ![p 2 ![a,b],p 1 ![c]]+
      q 2 ![p 1 ![b],p 2 ![a,c]]+
      q 2 ![p 1 ![a],p 2 ![b,c]]+
      q 1 ![p 3 ![a,b,c]] := by
  classical
  simp only [FormalMultilinearSeries.taylorComp,ContinuousMultilinearMap.sum_apply]
  rw [sum_partitions_three]
  congr 1
  · congr 1
    · congr 1
      · congr 1
        · simp only [FormalMultilinearSeries.compAlongOrderedFinpartition_apply,
            OrderedFinpartition.applyOrderedFinpartition_apply,
            OrderedFinpartition.extendLeft,OrderedFinpartition.atomic,Function.comp_def]
          congr 1
          funext m
          fin_cases m <;> congr 1 <;> ext j <;> fin_cases j <;> rfl
        · simp only [FormalMultilinearSeries.compAlongOrderedFinpartition_apply,
            OrderedFinpartition.applyOrderedFinpartition_apply,
            OrderedFinpartition.extendLeft,OrderedFinpartition.extendMiddle,
            OrderedFinpartition.atomic,Function.comp_def]
          congr 1
          funext m
          fin_cases m <;> congr 1 <;> ext j <;> fin_cases j <;> rfl
      · simp only [FormalMultilinearSeries.compAlongOrderedFinpartition_apply,
          OrderedFinpartition.applyOrderedFinpartition_apply,
          OrderedFinpartition.extendLeft,OrderedFinpartition.extendMiddle,
          OrderedFinpartition.atomic,Function.comp_def]
        congr 1
        funext m
        fin_cases m <;> congr 1 <;> ext j <;> fin_cases j <;> rfl
    · simp only [FormalMultilinearSeries.compAlongOrderedFinpartition_apply,
        OrderedFinpartition.applyOrderedFinpartition_apply,
        OrderedFinpartition.extendLeft,OrderedFinpartition.extendMiddle,
        OrderedFinpartition.atomic,Function.comp_def]
      congr 1
      funext m
      fin_cases m <;> congr 1 <;> ext j <;> fin_cases j <;> rfl
  · simp only [FormalMultilinearSeries.compAlongOrderedFinpartition_apply,
      OrderedFinpartition.applyOrderedFinpartition_apply,
      OrderedFinpartition.extendLeft,OrderedFinpartition.extendMiddle,
      OrderedFinpartition.atomic,Function.comp_def]
    congr 1
    funext m
    fin_cases m
    congr 1
    ext j
    fin_cases j <;> rfl

theorem taylorComp_two_apply (q : FormalMultilinearSeries ℝ F G)
    (p : FormalMultilinearSeries ℝ E F) (a b : E) :
    (q.taylorComp p 2) ![a,b]=q 2 ![p 1 ![a],p 1 ![b]]+q 1 ![p 2 ![a,b]] := by
  classical
  simp only [FormalMultilinearSeries.taylorComp,ContinuousMultilinearMap.sum_apply]
  rw [sum_partitions_two]
  congr 1
  · simp only [FormalMultilinearSeries.compAlongOrderedFinpartition_apply,
      OrderedFinpartition.applyOrderedFinpartition_apply,
      OrderedFinpartition.extendLeft,OrderedFinpartition.atomic,Function.comp_def]
    congr 1
    funext m
    fin_cases m <;> congr 1 <;> ext j <;> fin_cases j <;> rfl
  · simp only [FormalMultilinearSeries.compAlongOrderedFinpartition_apply,
      OrderedFinpartition.applyOrderedFinpartition_apply,
      OrderedFinpartition.extendLeft,OrderedFinpartition.extendMiddle,
      OrderedFinpartition.atomic,Function.comp_def]
    congr 1
    funext m
    fin_cases m
    congr 1
    ext j
    fin_cases j <;> rfl

theorem composition_second {g : F → G} {f : E → F} {x : E}
    (hg : ContDiffAt ℝ 2 g (f x)) (hf : ContDiffAt ℝ 2 f x) (a b : E) :
    iteratedFDeriv ℝ 2 (g ∘ f) x ![a,b]=
      iteratedFDeriv ℝ 2 g (f x)
        ![iteratedFDeriv ℝ 1 f x ![a],iteratedFDeriv ℝ 1 f x ![b]]+
      iteratedFDeriv ℝ 1 g (f x) ![iteratedFDeriv ℝ 2 f x ![a,b]] := by
  rw [iteratedFDeriv_comp hg hf (by rfl)]
  exact taylorComp_two_apply _ _ a b

theorem composition_third {g : F → G} {f : E → F} {x : E}
    (hg : ContDiffAt ℝ 3 g (f x)) (hf : ContDiffAt ℝ 3 f x) (a b c : E) :
    iteratedFDeriv ℝ 3 (g ∘ f) x ![a,b,c]=
      iteratedFDeriv ℝ 3 g (f x)
        ![iteratedFDeriv ℝ 1 f x ![a],iteratedFDeriv ℝ 1 f x ![b],
          iteratedFDeriv ℝ 1 f x ![c]]+
      iteratedFDeriv ℝ 2 g (f x)
        ![iteratedFDeriv ℝ 2 f x ![a,b],iteratedFDeriv ℝ 1 f x ![c]]+
      iteratedFDeriv ℝ 2 g (f x)
        ![iteratedFDeriv ℝ 1 f x ![b],iteratedFDeriv ℝ 2 f x ![a,c]]+
      iteratedFDeriv ℝ 2 g (f x)
        ![iteratedFDeriv ℝ 1 f x ![a],iteratedFDeriv ℝ 2 f x ![b,c]]+
      iteratedFDeriv ℝ 1 g (f x) ![iteratedFDeriv ℝ 3 f x ![a,b,c]] := by
  rw [iteratedFDeriv_comp hg hf (by rfl)]
  exact taylorComp_three_apply _ _ a b c

theorem composition_third_directional {g : F → G} {f : E → F} {x : E}
    (hg : ContDiffAt ℝ 3 g (f x)) (hf : ContDiffAt ℝ 3 f x) (a : E) :
    iteratedFDeriv ℝ 3 (g ∘ f) x ![a,a,a]=
      iteratedFDeriv ℝ 3 g (f x)
        ![iteratedFDeriv ℝ 1 f x ![a],iteratedFDeriv ℝ 1 f x ![a],
          iteratedFDeriv ℝ 1 f x ![a]]+
      (3:ℝ) • iteratedFDeriv ℝ 2 g (f x)
        ![iteratedFDeriv ℝ 2 f x ![a,a],iteratedFDeriv ℝ 1 f x ![a]]+
      iteratedFDeriv ℝ 1 g (f x) ![iteratedFDeriv ℝ 3 f x ![a,a,a]] := by
  rw [composition_third hg hf a a a]
  have hs := hg.isSymmSndFDerivAt (by norm_num [minSmoothness])
  rw [IsSymmSndFDerivAt.iteratedFDeriv_cons (hf := hs)
    (v := iteratedFDeriv ℝ 1 f x ![a]) (w := iteratedFDeriv ℝ 2 f x ![a,a])]
  module

end Chain

open FreeTransport SpatialCollision CollisionMultilinear CollisionFiber
abbrev RealPosition := Fin 3 → ℝ

def torusQuotient (x : RealPosition) : SpatialTorus := fun j => (x j : AddCircle period)

theorem torusQuotient_continuous : Continuous torusQuotient := by
  unfold torusQuotient
  fun_prop

/-- One real-coordinate lift, taking values in continuous momentum functions. -/
def realLift {R : ℝ} (f : Distribution R) : RealPosition → CubeFunction R :=
  fun x => momentumSection f (torusQuotient x)

theorem realLift_apply {R : ℝ} (f : Distribution R) (x : RealPosition)
    (k : MomentumDomain R) : realLift f x k=f (torusQuotient x,k) := rfl

theorem realLift_continuous {R : ℝ} (f : Distribution R) : Continuous (realLift f) :=
  f.curry.continuous.comp torusQuotient_continuous

theorem torusQuotient_update_period (x : RealPosition) (j : Fin 3) :
    torusQuotient (update x j (x j+period))=torusQuotient x := by
  classical
  funext i
  by_cases hi : i=j
  · subst i
    simp [torusQuotient]
  · simp [torusQuotient,update_of_ne hi]

theorem realLift_update_period {R : ℝ} (f : Distribution R)
    (x : RealPosition) (j : Fin 3) :
    realLift f (update x j (x j+period))=realLift f x := by
  unfold realLift
  rw [torusQuotient_update_period]

theorem realLift_collision_eq {R : ℝ} (hR : 0≤R) (f : Distribution R) :
    realLift (collision R hR f)=FiberContinuity.collisionMap R hR ∘ realLift f := by
  funext x
  ext k
  rfl

theorem realLift_collision_contDiff {R : ℝ} (hR : 0≤R) (f : Distribution R)
    {n : WithTop ℕ∞} (hf : ContDiff ℝ n (realLift f)) :
    ContDiff ℝ n (realLift (collision R hR f)) := by
  rw [realLift_collision_eq]
  exact (collisionMap_contDiff hR n).comp hf

theorem realLift_collision_first {R : ℝ} (hR : 0≤R) (f : Distribution R)
    (hf : ContDiff ℝ 3 (realLift f)) (x a : RealPosition) :
    fderiv ℝ (realLift (collision R hR f)) x a=
      ∑ i : Fin 3,collisionTrilinear R hR
        (update (fun _ => realLift f x) i (fderiv ℝ (realLift f) x a)) := by
  rw [realLift_collision_eq,
    fderiv_comp x (collisionMap_hasFDerivAt hR _).differentiableAt
      (hf.differentiable (by norm_num)).differentiableAt,
    ContinuousLinearMap.comp_apply,collisionMap_fderiv_apply]

theorem realLift_collision_second {R : ℝ} (hR : 0≤R) (f : Distribution R)
    (hf : ContDiff ℝ 3 (realLift f)) (x a b : RealPosition) :
    iteratedFDeriv ℝ 2 (realLift (collision R hR f)) x ![a,b]=
      iteratedFDeriv ℝ 2 (FiberContinuity.collisionMap R hR) (realLift f x)
        ![iteratedFDeriv ℝ 1 (realLift f) x ![a],iteratedFDeriv ℝ 1 (realLift f) x ![b]]+
      iteratedFDeriv ℝ 1 (FiberContinuity.collisionMap R hR) (realLift f x)
        ![iteratedFDeriv ℝ 2 (realLift f) x ![a,b]] := by
  rw [realLift_collision_eq]
  exact composition_second (collisionMap_contDiff hR 2).contDiffAt
    ((hf.of_le (by norm_num)).contDiffAt) a b

/-- All five third-order blocks, with the three mixed blocks kept separately. -/
theorem realLift_collision_third {R : ℝ} (hR : 0≤R) (f : Distribution R)
    (hf : ContDiff ℝ 3 (realLift f)) (x a b c : RealPosition) :
    iteratedFDeriv ℝ 3 (realLift (collision R hR f)) x ![a,b,c]=
      iteratedFDeriv ℝ 3 (FiberContinuity.collisionMap R hR) (realLift f x)
        ![iteratedFDeriv ℝ 1 (realLift f) x ![a],iteratedFDeriv ℝ 1 (realLift f) x ![b],
          iteratedFDeriv ℝ 1 (realLift f) x ![c]]+
      iteratedFDeriv ℝ 2 (FiberContinuity.collisionMap R hR) (realLift f x)
        ![iteratedFDeriv ℝ 2 (realLift f) x ![a,b],iteratedFDeriv ℝ 1 (realLift f) x ![c]]+
      iteratedFDeriv ℝ 2 (FiberContinuity.collisionMap R hR) (realLift f x)
        ![iteratedFDeriv ℝ 1 (realLift f) x ![b],iteratedFDeriv ℝ 2 (realLift f) x ![a,c]]+
      iteratedFDeriv ℝ 2 (FiberContinuity.collisionMap R hR) (realLift f x)
        ![iteratedFDeriv ℝ 1 (realLift f) x ![a],iteratedFDeriv ℝ 2 (realLift f) x ![b,c]]+
      iteratedFDeriv ℝ 1 (FiberContinuity.collisionMap R hR) (realLift f x)
        ![iteratedFDeriv ℝ 3 (realLift f) x ![a,b,c]] := by
  rw [realLift_collision_eq]
  exact composition_third (collisionMap_contDiff hR 3).contDiffAt hf.contDiffAt a b c

theorem realLift_collision_third_directional {R : ℝ} (hR : 0≤R) (f : Distribution R)
    (hf : ContDiff ℝ 3 (realLift f)) (x a : RealPosition) :
    iteratedFDeriv ℝ 3 (realLift (collision R hR f)) x ![a,a,a]=
      iteratedFDeriv ℝ 3 (FiberContinuity.collisionMap R hR) (realLift f x)
        ![iteratedFDeriv ℝ 1 (realLift f) x ![a],iteratedFDeriv ℝ 1 (realLift f) x ![a],
          iteratedFDeriv ℝ 1 (realLift f) x ![a]]+
      (3:ℝ) • iteratedFDeriv ℝ 2 (FiberContinuity.collisionMap R hR) (realLift f x)
        ![iteratedFDeriv ℝ 2 (realLift f) x ![a,a],iteratedFDeriv ℝ 1 (realLift f) x ![a]]+
      iteratedFDeriv ℝ 1 (FiberContinuity.collisionMap R hR) (realLift f x)
        ![iteratedFDeriv ℝ 3 (realLift f) x ![a,a,a]] := by
  rw [realLift_collision_eq]
  exact composition_third_directional (collisionMap_contDiff hR 3).contDiffAt hf.contDiffAt a

theorem collision_jet_apply_bound {R : ℝ} (hR : 0≤R) (n : ℕ)
    (u : CubeFunction R) (v : Fin n → CubeFunction R) :
    ‖iteratedFDeriv ℝ n (FiberContinuity.collisionMap R hR) u v‖≤
      (Nat.descFactorial 3 n : ℝ)*(4*(fiberMassBound R).toReal)*‖u‖^(3-n)*∏ j,‖v j‖ := by
  exact (iteratedFDeriv ℝ n (FiberContinuity.collisionMap R hR) u).le_opNorm v |>.trans
    (mul_le_mul_of_nonneg_right (collisionMap_iteratedFDeriv_norm_le hR n u) (by positivity))

#check sum_partition_succ
#print axioms sum_partition_succ
#check sum_partitions_one
#print axioms sum_partitions_one
#check sum_partitions_two
#print axioms sum_partitions_two
#check sum_partitions_three
#print axioms sum_partitions_three
#check taylorComp_three_apply
#print axioms taylorComp_three_apply
#check taylorComp_two_apply
#print axioms taylorComp_two_apply
#check composition_second
#print axioms composition_second
#check composition_third
#print axioms composition_third
#check composition_third_directional
#print axioms composition_third_directional
#check torusQuotient_continuous
#print axioms torusQuotient_continuous
#check realLift_apply
#print axioms realLift_apply
#check realLift_continuous
#print axioms realLift_continuous
#check torusQuotient_update_period
#print axioms torusQuotient_update_period
#check realLift_update_period
#print axioms realLift_update_period
#check realLift_collision_eq
#print axioms realLift_collision_eq
#check realLift_collision_contDiff
#print axioms realLift_collision_contDiff
#check realLift_collision_first
#print axioms realLift_collision_first
#check realLift_collision_second
#print axioms realLift_collision_second
#check realLift_collision_third
#print axioms realLift_collision_third
#check realLift_collision_third_directional
#print axioms realLift_collision_third_directional
#check collision_jet_apply_bound
#print axioms collision_jet_apply_bound

end
end Resonance.SpatialChainRule
