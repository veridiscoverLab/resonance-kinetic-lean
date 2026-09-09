import Resonance.ContinuousRegularizedEquation
import Resonance.OneWeightedPairReadout

/-! The actual two-norm space on C(D), realized as the closed graph
of q ↦ s ν_* q. Its norm is max(||q||, |s| ||ν_* q||). -/
open Set
namespace Resonance.RegularizedGraphNorm
noncomputable section
open ResonantMeasure OneWeightedPairReadout
abbrev X (R : ℝ) := C(cube R,ℝ)

def weightMap {R : ℝ} (hR : 0≤R) : X R→L[ℝ]X R :=
  ContinuousLinearMap.mul ℝ (X R) (referenceContinuous hR)

def constraint {R : ℝ} (hR : 0≤R) (s : ℝ) : (X R×X R)→L[ℝ]X R :=
  ContinuousLinearMap.snd ℝ (X R) (X R)-
    s • (weightMap hR).comp (ContinuousLinearMap.fst ℝ (X R) (X R))

def graphSpace {R : ℝ} (hR : 0≤R) (s : ℝ) : Submodule ℝ (X R×X R) :=
  (constraint hR s).ker

instance graph_complete {R : ℝ} (hR : 0≤R) (s : ℝ) : CompleteSpace (graphSpace hR s) :=
  (constraint hR s).isClosed_ker.completeSpace_coe

def lift {R : ℝ} (hR : 0≤R) (s : ℝ) (q : X R) : graphSpace hR s :=
  ⟨(q,s • (referenceContinuous hR*q)),by
    change s • (referenceContinuous hR*q)-s • (referenceContinuous hR*q)=0
    exact sub_self _⟩

def read {R : ℝ} {hR : 0≤R} {s : ℝ} (q : graphSpace hR s) : X R := q.val.1

theorem read_lift {R : ℝ} (hR : 0≤R) (s : ℝ) (q : X R) : read (lift hR s q)=q := rfl

theorem second_eq {R : ℝ} {hR : 0≤R} {s : ℝ} (q : graphSpace hR s) :
    q.val.2=s • (referenceContinuous hR*read q) := by
  have h := q.property
  change q.val.2-s • (referenceContinuous hR*read q)=0 at h
  exact sub_eq_zero.mp h

theorem lift_read {R : ℝ} {hR : 0≤R} {s : ℝ} (q : graphSpace hR s) : lift hR s (read q)=q := by
  apply Subtype.ext
  change (read q,s • (referenceContinuous hR*read q))=q.val
  exact Prod.ext rfl (second_eq q).symm

theorem read_injective {R : ℝ} {hR : 0≤R} {s : ℝ} :
    Function.Injective (@read R hR s) := by
  intro q r h
  rw [←lift_read q,←lift_read r,h]

theorem norm_eq {R : ℝ} {hR : 0≤R} {s : ℝ} (q : graphSpace hR s) :
    ‖q‖=max ‖read q‖ (|s| * ‖referenceContinuous hR*read q‖) := by
  change max ‖q.val.1‖ ‖q.val.2‖=_
  rw [second_eq,norm_smul,Real.norm_eq_abs]
  rfl

theorem read_norm_le {R : ℝ} {hR : 0≤R} {s : ℝ} (q : graphSpace hR s) : ‖read q‖≤‖q‖ := by
  rw [norm_eq]
  exact le_max_left _ _

theorem weighted_norm_le {R : ℝ} {hR : 0≤R} {s : ℝ} (hs : 0 ≤ s) (q : graphSpace hR s) :
    s*‖referenceContinuous hR*read q‖≤‖q‖ := by
  rw [norm_eq,abs_of_nonneg hs]
  exact le_max_right _ _

theorem norm_lift_le {R : ℝ} (hR : 0≤R) {s B : ℝ} (hs : 0 ≤ s) (q : X R)
    (h0 : ‖q‖≤B) (h1 : s*‖referenceContinuous hR*q‖≤B) : ‖lift hR s q‖≤B := by
  rw [norm_eq,read_lift,abs_of_nonneg hs]
  exact max_le h0 h1

theorem read_sub {R : ℝ} {hR : 0≤R} {s : ℝ} (q r : graphSpace hR s) :
    read (q-r)=read q-read r := rfl

theorem lift_sub {R : ℝ} (hR : 0≤R) (s : ℝ) (q r : X R) :
    lift hR s (q-r)=lift hR s q-lift hR s r := by
  apply read_injective
  rfl

end
end Resonance.RegularizedGraphNorm
