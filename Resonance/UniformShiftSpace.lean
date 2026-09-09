import Resonance.StrongCellBanachSmooth
import Mathlib.Analysis.Normed.Lp.lpSpace

/-! The actual bounded shift interval with its supremum Banach norm.
No continuity in the shift is imposed on the unweighted loss multiplier. -/
open Set
open scoped ENNReal ContDiff
namespace Resonance.UniformShiftSpace
noncomputable section
set_option maxHeartbeats 1800000
set_option synthInstance.maxHeartbeats 200000
open LinftyMultiplication

abbrev Shift := Set.Icc (0:ℝ) 1
abbrev Op (R : ℝ) := X R→L[ℝ]X R
abbrev Family (R : ℝ) := lp (fun _ : Shift=>Op R) ∞

/- The fibers are all the same operator algebra. Its identity is
uniformly bounded even when the underlying cube space is trivial. -/
def familySubring (R : ℝ) : Subring (PreLp (fun _ : Shift=>Op R)) :=
  { lp (fun _ : Shift=>Op R) ∞ with
    carrier := {f | Memℓp f ∞}
    one_mem' := memℓp_infty ⟨‖(1 : Op R)‖,by rintro _ ⟨z,rfl⟩; exact le_rfl⟩
    mul_mem' := Memℓp.infty_mul }

instance familyRing (R : ℝ) : Ring (Family R) := inferInstanceAs (Ring (familySubring R))

instance familyNormedRing (R : ℝ) : NormedRing (Family R) :=
  { familyRing R,lp.nonUnitalNormedRing with }

def familySubalgebra (R : ℝ) : Subalgebra ℝ (PreLp (fun _ : Shift=>Op R)) :=
  { familySubring R with
    carrier := {f | Memℓp f ∞}
    algebraMap_mem' := fun a=>memℓp_infty ⟨‖algebraMap ℝ (Op R) a‖,by
      rintro _ ⟨z,rfl⟩; exact le_rfl⟩ }

instance familyAlgebra (R : ℝ) : Algebra ℝ (Family R) :=
  inferInstanceAs (Algebra ℝ (familySubalgebra R))

instance familyNormedAlgebra (R : ℝ) : NormedAlgebra ℝ (Family R) where
  norm_smul_le a f := by
    apply lp.norm_le_of_forall_le (mul_nonneg (norm_nonneg a) (norm_nonneg f))
    intro z
    exact (norm_smul_le a (f z)).trans (mul_le_mul_of_nonneg_left
      (lp.norm_apply_le_norm ENNReal.top_ne_zero f z) (norm_nonneg a))

def ofBound (R : ℝ) (f : Shift→Op R) (C : ℝ) (hf : ∀z,‖f z‖≤C) : Family R :=
  ⟨f,memℓp_infty ⟨C,by rintro _ ⟨z,rfl⟩; exact hf z⟩⟩

theorem ofBound_apply (R : ℝ) (f : Shift→Op R) (C : ℝ) (hf : ∀z,‖f z‖≤C) (z : Shift) :
    ofBound R f C hf z=f z := rfl

def constLinear (R : ℝ) : Op R→ₗ[ℝ]Family R where
  toFun A := ofBound R (fun _=>A) ‖A‖ (fun _=>le_rfl)
  map_add' _ _ := lp.ext rfl
  map_smul' _ _ := lp.ext rfl

def constMap (R : ℝ) : Op R→L[ℝ]Family R :=
  (constLinear R).mkContinuous 1 (fun A=>by
    simpa only [one_mul] using lp.norm_le_of_forall_le (norm_nonneg A) (fun _=>le_rfl))

theorem constMap_apply (R : ℝ) (A : Op R) (z : Shift) : constMap R A z=A := rfl

def evalLinear (R : ℝ) (z : Shift) : Family R→ₗ[ℝ]Op R where
  toFun A := A z
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def evalMap (R : ℝ) (z : Shift) : Family R→L[ℝ]Op R :=
  (evalLinear R z).mkContinuous 1 (fun A=>by
    simpa only [one_mul] using lp.norm_apply_le_norm ENNReal.top_ne_zero A z)

theorem evalMap_apply (R : ℝ) (z : Shift) (A : Family R) : evalMap R z A=A z := rfl

theorem evalMap_norm_le (R : ℝ) (z : Shift) : ‖evalMap R z‖≤1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro A
  simpa only [one_mul] using lp.norm_apply_le_norm ENNReal.top_ne_zero A z

end
end Resonance.UniformShiftSpace
