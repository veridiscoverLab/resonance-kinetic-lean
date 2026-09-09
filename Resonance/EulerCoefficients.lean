import Resonance.ThermodynamicJets

/-! Actual five-moment Euler fluxes and their positive symmetrizer on the
original positive RJ parameter domain. This supplies coefficient geometry;
it does not assume or assert a PDE existence theorem. -/
open MeasureTheory
open scoped BigOperators ContDiff Matrix.Norms.Elementwise

namespace Resonance.EulerCoefficients
noncomputable section
open Entropy Thermodynamics ThermodynamicJets

def fluxWeight (j : Fin 3) (i : Fin 5) (k : Momentum) : ℝ :=
  (2 * k j) * fiveInvariants i k

theorem fluxWeight_continuous (j : Fin 3) (i : Fin 5) : Continuous (fluxWeight j i) :=
  (continuous_const.mul (continuous_apply j)).mul (fiveInvariants_continuous i)

def fluxMap (R : ℝ) (j : Fin 3) (θ : Parameter) : Parameter :=
  fun i => powerIntegral R 0 (fluxWeight j i) θ

theorem fluxMap_integral (R : ℝ) (j : Fin 3) (θ : Parameter) (i : Fin 5) :
    fluxMap R j θ i = ∫ k, (2 * k j) * fiveInvariants i k * rj fiveInvariants θ k
      ∂cubeMeasure R := by simp only [fluxMap, powerIntegral, fluxWeight, zero_add, pow_one]

def fluxMatrix (R : ℝ) (j : Fin 3) (θ : Parameter) : Matrix (Fin 5) (Fin 5) ℝ :=
  fun i l => powerIntegral R 1 (fun k => fluxWeight j i k * fiveInvariants l k) θ

theorem fluxMatrix_integral (R : ℝ) (j : Fin 3) (θ : Parameter) (i l : Fin 5) :
    fluxMatrix R j θ i l = ∫ k, (2 * k j) * fiveInvariants i k * fiveInvariants l k *
      (rj fiveInvariants θ k) ^ 2 ∂cubeMeasure R := rfl

def fluxDerivative (R : ℝ) (j : Fin 3) (θ : Parameter) : Parameter →L[ℝ] Parameter :=
  ContinuousLinearMap.pi (fun i => powerDerivative R 0 (fluxWeight j i) θ)

theorem fluxMap_hasFDerivAt (R : ℝ) (j : Fin 3) (θ : Parameter)
    (hθ : θ ∈ positiveDomain R) :
    HasFDerivAt (fluxMap R j) (fluxDerivative R j θ) θ :=
  hasFDerivAt_pi.mpr (fun i => powerIntegral_hasFDerivAt R 0 (fluxWeight j i)
    (fluxWeight_continuous j i) θ hθ)

theorem fluxDerivative_apply (R : ℝ) (j : Fin 3) (θ b : Parameter) (i : Fin 5) :
    fluxDerivative R j θ b i = -(fluxMatrix R j θ).mulVec b i := by
  simp [fluxDerivative, powerDerivative, fluxMatrix, Matrix.mulVec, dotProduct,
    Finset.sum_neg_distrib]

theorem fluxMatrix_isHermitian (R : ℝ) (j : Fin 3) (θ : Parameter) :
    (fluxMatrix R j θ).IsHermitian := by
  ext i l
  change fluxMatrix R j θ l i = fluxMatrix R j θ i l
  simp only [fluxMatrix_integral]
  apply integral_congr_ae
  filter_upwards [] with k
  ring

theorem fluxMap_contDiffOn_finite (R : ℝ) (j : Fin 3) (n : ℕ) :
    ContDiffOn ℝ n (fluxMap R j) (positiveDomain R) :=
  contDiffOn_pi.mpr (fun i => powerIntegral_contDiffOn_finite R n 0 (fluxWeight j i)
    (fluxWeight_continuous j i))

theorem fluxMap_contDiffOn_infty (R : ℝ) (j : Fin 3) :
    ContDiffOn ℝ ∞ (fluxMap R j) (positiveDomain R) :=
  contDiffOn_infty.mpr (fluxMap_contDiffOn_finite R j)

theorem fluxMatrix_contDiffOn_finite (R : ℝ) (j : Fin 3) (n : ℕ) :
    ContDiffOn ℝ n (fluxMatrix R j) (positiveDomain R) := by
  apply contDiffOn_pi.mpr
  intro i
  apply contDiffOn_pi.mpr
  intro l
  exact powerIntegral_contDiffOn_finite R n 1
    (fun k => fluxWeight j i k * fiveInvariants l k)
    ((fluxWeight_continuous j i).mul (fiveInvariants_continuous l))

/-- The same actual moment matrix is positive definite and symmetrizes all
three actual flux derivatives throughout the positive parameter domain. -/
theorem symmetric_euler_coefficients (R : ℝ) (hR : 0 < R) (θ : Parameter)
    (hθ : θ ∈ positiveDomain R) :
    (gramMatrix R θ).PosDef ∧ ∀ j : Fin 3, (fluxMatrix R j θ).IsHermitian :=
  ⟨gramMatrix_posDef R hR θ hθ, fun j => fluxMatrix_isHermitian R j θ⟩

end
end Resonance.EulerCoefficients
