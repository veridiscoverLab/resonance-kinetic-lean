import Resonance.RegularizedContinuousOutput
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-! The actual positive Rayleigh--Jeans profile is a C-infinity map into
C of the whole closed cube, by the genuine Banach algebra inverse of its
linear five-moment denominator. -/
open Set
open scoped Topology BigOperators ContDiff
namespace Resonance.ProfileBanachSmooth
noncomputable section
set_option maxHeartbeats 1000000
open ResonantMeasure Thermodynamics WeightedJointMeasure
open CoareaNormalization (euclideanFive euclideanFive_continuous euclidean_rj_coordinate)
open StrongCellParameterContinuity (profileContinuous)

def invariantContinuous (R : ℝ) (i : Fin 5) : C(cube R,ℝ) :=
  ⟨fun k=>euclideanFive i k,(euclideanFive_continuous i).comp continuous_subtype_val⟩

def denominatorMap (R : ℝ) : Parameter→L[ℝ]C(cube R,ℝ) :=
  ∑i : Fin 5,(ContinuousLinearMap.proj i).smulRight (invariantContinuous R i)

theorem denominatorMap_apply (R : ℝ) (θ : Parameter) (k : cube R) :
    denominatorMap R θ k=Entropy.denominator euclideanFive θ k := by
  simp [denominatorMap,invariantContinuous,Entropy.denominator]

theorem profile_eq_inverse_denominator (θ : Parameter) (k : E) :
    profile θ k=(Entropy.denominator euclideanFive θ k)⁻¹ := by
  have he := euclidean_rj_coordinate θ (coordinates k)
  change Entropy.rj euclideanFive θ k=profile θ k at he
  exact he.symm

def denominatorUnit {R : ℝ} {θ : Parameter} (hθ : θ∈positiveDomain R) : C(cube R,ℝ)ˣ where
  val := denominatorMap R θ
  inv := profileContinuous hθ
  val_inv := by
    ext k
    change denominatorMap R θ k*profile θ k=1
    rw [denominatorMap_apply,profile_eq_inverse_denominator]
    apply mul_inv_cancel₀
    have hp := profile_pos hθ k.property
    rw [profile_eq_inverse_denominator] at hp
    exact (inv_pos.mp hp).ne'
  inv_val := by
    ext k
    change profile θ k*denominatorMap R θ k=1
    rw [denominatorMap_apply,profile_eq_inverse_denominator]
    apply inv_mul_cancel₀
    have hp := profile_pos hθ k.property
    rw [profile_eq_inverse_denominator] at hp
    exact (inv_pos.mp hp).ne'

def profileMap (R : ℝ) (θ : Parameter) : C(cube R,ℝ) := Ring.inverse (denominatorMap R θ)

theorem profileMap_eq {R : ℝ} {θ : Parameter} (hθ : θ∈positiveDomain R) :
    profileMap R θ=profileContinuous hθ := Ring.inverse_unit (denominatorUnit hθ)

theorem profileMap_apply {R : ℝ} {θ : Parameter} (hθ : θ∈positiveDomain R) (k : cube R) :
    profileMap R θ k=profile θ k := by rw [profileMap_eq hθ]; rfl

theorem profileMap_contDiffAt {R : ℝ} {θ : Parameter} (hθ : θ∈positiveDomain R) :
    ContDiffAt ℝ ∞ (profileMap R) θ := by
  have hi := contDiffAt_ringInverse (𝕜:=ℝ) (n:=∞) (denominatorUnit hθ)
  exact hi.comp θ (denominatorMap R).contDiff.contDiffAt

theorem actual_profileMap_contDiffOn (R : ℝ) :
    ContDiffOn ℝ ∞ (profileMap R) (positiveDomain R) :=
  fun _ hθ=>(profileMap_contDiffAt hθ).contDiffWithinAt

end
end Resonance.ProfileBanachSmooth
