import Resonance.WeightedPhysicalForm
import Resonance.PolarCoordinates

/-! Exact differentiation of the original cubic four-parent polynomial,
with its complete Rayleigh--Jeans reciprocal collision relation. -/
open MeasureTheory Set
open scoped ENNReal

namespace Resonance.CollisionLinearization
noncomputable section
open Collision ResonantMeasure Thermodynamics

def linearCoefficient (N h : Quartet) : ℝ :=
  (N 2 * N 3 - N 1 * N 3 - N 1 * N 2) * h 0 +
  (N 2 * N 3 - N 0 * N 3 - N 0 * N 2) * h 1 +
  (N 1 * N 3 + N 0 * N 3 - N 0 * N 1) * h 2 +
  (N 1 * N 2 + N 0 * N 2 - N 0 * N 1) * h 3

theorem collisionPolynomial_derivative (N h : Quartet) :
    HasDerivAt (fun t : ℝ => collisionPolynomial (fun i => N i + t * h i))
      (linearCoefficient N h) 0 := by
  have hd (i : Fin 4) : HasDerivAt (fun t : ℝ => N i + t * h i) (h i) 0 := by
    simpa using (((hasDerivAt_id (0 : ℝ)).mul_const (h i)).const_add (N i))
  convert ((((hd 1).mul (hd 2)).mul (hd 3)).add
    (((hd 0).mul (hd 2)).mul (hd 3))).sub
    (((hd 0).mul (hd 1)).mul (hd 3)) |>.sub
    (((hd 0).mul (hd 1)).mul (hd 2)) using 1
  simp only [Pi.mul_apply, zero_mul, add_zero]
  dsimp [linearCoefficient]
  ring

theorem collisionPolynomial_exact_cubic (N h : Quartet) (t : ℝ) :
    collisionPolynomial (fun i => N i + t * h i) = collisionPolynomial N +
      t * linearCoefficient N h + t ^ 2 * linearCoefficient h N + t ^ 3 * collisionPolynomial h := by
  dsimp [collisionPolynomial, linearCoefficient]
  ring

theorem relative_linearization_identity (N h : Quartet) (hN : ∀ i, N i ≠ 0) :
    linearCoefficient N (fun i => N i * h i) =
      (h 0 + h 1 + h 2 + h 3) * collisionPolynomial N -
        mobility N * delta (fun i => h i / N i) := by
  dsimp [linearCoefficient, collisionPolynomial, mobility, delta]
  field_simp [hN 0, hN 1, hN 2, hN 3]
  ring

theorem equilibrium_linearization (N h : Quartet) (hN : ∀ i, N i ≠ 0)
    (heq : delta (fun i => (N i)⁻¹) = 0) :
    linearCoefficient N (fun i => N i * h i) =
      -mobility N * delta (fun i => h i / N i) := by
  rw [relative_linearization_identity N h hN, collision_reciprocal_identity N hN, heq]
  ring

theorem equilibrium_weak_derivative (N h g : Quartet) (hN : ∀ i, N i ≠ 0)
    (heq : delta (fun i => (N i)⁻¹) = 0) :
    HasDerivAt (fun t : ℝ => quarterPairing (fun i => N i + t * (N i * h i))
      (fun i => g i / N i))
      (-(1 / 4 : ℝ) * mobility N * delta (fun i => h i / N i) *
        delta (fun i => g i / N i)) 0 := by
  have hd := ((collisionPolynomial_derivative N (fun i => N i * h i)).const_mul
    (1 / 4 : ℝ)).mul_const (delta (fun i => g i / N i))
  simpa only [signed_parent_pairing, equilibrium_linearization N h hN heq, mul_neg,
    neg_mul, mul_assoc] using hd

theorem reciprocalProfile_expanded (θ : Parameter) (k : E) :
    WeightedPhysicalForm.reciprocalProfile θ k =
      θ 0 + θ 1 * k 0 + θ 2 * k 1 + θ 3 * k 2 + θ 4 * ‖k‖ ^ 2 := by
  have hc := CoareaNormalization.euclidean_denominator_coordinate θ
    (WeightedJointMeasure.coordinates k)
  change Entropy.denominator Entropy.fiveInvariants θ (WeightedJointMeasure.coordinates k) = _
  rw [← hc]
  have he : CoareaNormalization.toMomentumE (WeightedJointMeasure.coordinates k) = k := rfl
  rw [he]
  simp [Entropy.denominator, CoareaNormalization.euclideanFive, Fin.sum_univ_succ]
  ring

theorem reciprocalProfile_full_relation (θ : Parameter) (k : FourMomenta)
    (hm : k 0 + k 1 = k 2 + k 3)
    (he : ‖k 0‖ ^ 2 + ‖k 1‖ ^ 2 = ‖k 2‖ ^ 2 + ‖k 3‖ ^ 2) :
    delta (fun i => WeightedPhysicalForm.reciprocalProfile θ (k i)) = 0 := by
  have hx (j : Fin 3) : k 0 j + k 1 j = k 2 j + k 3 j := by
    exact congrArg (fun p : E => p j) hm
  simp only [delta, reciprocalProfile_expanded]
  have h0 := congrArg (fun x : ℝ => θ 1 * x) (hx 0)
  have h1 := congrArg (fun x : ℝ => θ 2 * x) (hx 1)
  have h2 := congrArg (fun x : ℝ => θ 3 * x) (hx 2)
  have hE := congrArg (fun x : ℝ => θ 4 * x) he
  nlinarith

theorem rj_reciprocal_relation_ae (R : ℝ) (θ : Parameter) :
    ∀ᵐ k ∂pairingMeasure R,
      delta (fun i => (WeightedJointMeasure.profile θ (k i))⁻¹) = 0 := by
  filter_upwards [ae_iff.mpr (pairing_supported_on_fullResonance R)] with k hk
  simpa only [WeightedPhysicalForm.reciprocalProfile_eq_inv] using
    reciprocalProfile_full_relation θ k hk.2.1 hk.2.2

theorem rj_collision_equilibrium_ae {R : ℝ} {θ : Parameter} (hθ : θ ∈ positiveDomain R) :
    ∀ᵐ k ∂pairingMeasure R,
      collisionPolynomial (fun i => WeightedJointMeasure.profile θ (k i)) = 0 := by
  filter_upwards [ae_iff.mpr (pairing_supported_on_fullResonance R),
    rj_reciprocal_relation_ae R θ] with k hk he
  rw [collision_reciprocal_identity _ (fun i => (WeightedJointMeasure.profile_pos hθ (hk.1 i)).ne'), he,
    mul_zero]

end
end Resonance.CollisionLinearization
