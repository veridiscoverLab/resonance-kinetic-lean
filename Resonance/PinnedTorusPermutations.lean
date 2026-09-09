import Resonance.PinnedCircleMollifier
import Mathlib.MeasureTheory.Measure.Haar.Unique

/-! Actual integer-linear incoming, outgoing, and pair exchanges on the
original three-torus. Probability Haar preservation is proved from the
actual continuous additive automorphisms, not from a surface-area assertion. -/
open Set MeasureTheory
namespace Resonance.PinnedTorusPermutations
noncomputable section
open PinnedPeriodicity PinnedClassificationFinal PinnedLegACCircle PinnedMaximalDifference
open PinnedCircleMollifier
local instance periodPositive : Fact (0<period) := ⟨period_pos⟩

def transform (j : Fin 3) : CircleMomenta →+ CircleMomenta where
  toFun k := ![![k 1,k 0,k 2],![k 0,k 1,k 0+k 1-k 2],![k 2,k 0+k 1-k 2,k 0]] j
  map_zero' := by ext i; fin_cases j <;> fin_cases i <;> simp
  map_add' k l := by
    ext i
    fin_cases j <;> fin_cases i <;> simp <;> abel

theorem transform_involutive (j : Fin 3) : Function.Involutive (transform j) := by
  intro k
  ext i
  fin_cases j <;> fin_cases i <;> simp [transform]

theorem transform_continuous (j : Fin 3) : Continuous (transform j) := by
  apply continuous_pi
  intro i
  fin_cases j <;> fin_cases i <;> dsimp [transform]
  all_goals fun_prop

def equivalence (j : Fin 3) : CircleMomenta ≃ₜ+ CircleMomenta where
  toFun := transform j
  invFun := transform j
  left_inv := transform_involutive j
  right_inv := transform_involutive j
  map_add' := (transform j).map_add
  continuous_toFun := transform_continuous j
  continuous_invFun := transform_continuous j

theorem transform_preserving (j : Fin 3) : MeasurePreserving (transform j)
    (Measure.pi (fun _:Fin 3=>circleHaar)) (Measure.pi (fun _:Fin 3=>circleHaar)) :=
  AddMonoidHom.measurePreserving (transform_continuous j) (transform_involutive j).surjective rfl

def permuted (j : Fin 3) (q : FourCircle) : FourCircle :=
  ![![q 1,q 0,q 2,q 3],![q 0,q 1,q 3,q 2],![q 2,q 3,q 0,q 1]] j

theorem fullLegs_transform (j : Fin 3) (k : CircleMomenta) :
    fullLegs (transform j k)=permuted j (fullLegs k) := by
  ext i
  fin_cases j <;> fin_cases i <;> simp [fullLegs,circleLeg,transform,permuted]
  all_goals abel

def sign (j : Fin 3) : ℝ := if j=2 then -1 else 1

def legIndex (j : Fin 3) (i : Fin 4) : Fin 4 :=
  ![![1,0,2,3],![0,1,3,2],![2,3,0,1]] j i

theorem leg_transform (j : Fin 3) (i : Fin 4) (k : CircleMomenta) :
    circleLeg i (transform j k)=circleLeg (legIndex j i) k := by
  have he := congrFun (fullLegs_transform j k) i
  change circleLeg i (transform j k)=permuted j (fullLegs k) i at he
  rw [he]
  fin_cases j <;> fin_cases i <;> rfl

theorem difference_transform (j : Fin 3) (φ : PinnedPeriodicity.Circle→ℂ) (k : CircleMomenta) :
    difference φ (transform j k)=(sign j:ℂ)*difference φ k := by
  have he := fullLegs_transform j k
  have hi : ∀i:Fin 4,circleLeg i (transform j k)=permuted j (fullLegs k) i :=
    fun i=>congrFun he i
  simp only [difference,hi]
  fin_cases j <;> simp [sign,permuted,fullLegs] <;> ring

theorem energy_transform (j : Fin 3) (d : ℝ) (k : CircleMomenta) :
    energy d (transform j k)=sign j*energy d k := by
  have he := fullLegs_transform j k
  have hi : ∀i:Fin 4,circleLeg i (transform j k)=permuted j (fullLegs k) i :=
    fun i=>congrFun he i
  simp only [energy,hi]
  fin_cases j <;> simp [sign,permuted,fullLegs] <;> ring

def SymmetricWeight (a : FourCircle→ℝ) : Prop := ∀j q,a (permuted j q)=a q

theorem symmetric_weight_transform {a : FourCircle→ℝ} (ha : SymmetricWeight a)
    (j : Fin 3) (k : CircleMomenta) : a (fullLegs (transform j k))=a (fullLegs k) := by
  rw [fullLegs_transform,ha]

end
end Resonance.PinnedTorusPermutations
