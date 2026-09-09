import Resonance.ResonantMeasure

/-!
The entire four-leg difference on the concrete global pairing measure. The same
one-leg marginal defines the input L² space, and all pullbacks land in one joint
L² space. This constructs its bounded, nonnegative self-adjoint square; the
physical coarea identity and the classification of its null space remain separate.
The operator is an adjoint square in the marginal-weighted Hilbert space, NOT the
unweighted physical collision generator L_N; their identification is not claimed.
-/
namespace Resonance.CollisionForm

open MeasureTheory
open Resonance.ResonantMeasure
open scoped Topology

noncomputable section

def marginal (R : ℝ) : Measure E :=
  Measure.map (fun k : FourMomenta => k 0) (pairingMeasure R)

theorem all_legs_preserve (R : ℝ) (i : Fin 4) :
    MeasurePreserving (fun k : FourMomenta => k i) (pairingMeasure R) (marginal R) := by
  have h0 : MeasurePreserving (fun k : FourMomenta => k 0) (pairingMeasure R) (marginal R) :=
    ⟨measurable_pi_apply 0, rfl⟩
  have h1 : MeasurePreserving (fun k : FourMomenta => k 1) (pairingMeasure R) (marginal R) := by
    simpa [Function.comp_def, swapIncomingK] using h0.comp (incoming_preserves_pairing R)
  have h2 : MeasurePreserving (fun k : FourMomenta => k 2) (pairingMeasure R) (marginal R) := by
    simpa [Function.comp_def, swapPairsK] using h0.comp (pairs_preserves_pairing R)
  have h3 : MeasurePreserving (fun k : FourMomenta => k 3) (pairingMeasure R) (marginal R) := by
    simpa [Function.comp_def, swapPairsK] using h1.comp (pairs_preserves_pairing R)
  fin_cases i
  · exact h0
  · exact h1
  · exact h2
  · exact h3

abbrev H (R : ℝ) := Lp ℝ 2 (marginal R)
abbrev J (R : ℝ) := Lp ℝ 2 (pairingMeasure R)

def pullback (R : ℝ) (i : Fin 4) : H R →ₗᵢ[ℝ] J R :=
  Lp.compMeasurePreservingₗᵢ ℝ (fun k : FourMomenta => k i) (all_legs_preserve R i)

theorem pullback_ae (R : ℝ) (i : Fin 4) (f : H R) :
    pullback R i f =ᵐ[pairingMeasure R] (fun k => f (k i)) :=
  Lp.coeFn_compMeasurePreserving f (all_legs_preserve R i)

def fullDifference (R : ℝ) : H R →L[ℝ] J R :=
  (1/2 : ℝ) • ((pullback R 0).toContinuousLinearMap + (pullback R 1).toContinuousLinearMap -
    (pullback R 2).toContinuousLinearMap - (pullback R 3).toContinuousLinearMap)

def rawDifference (f : E → ℝ) (k : FourMomenta) : ℝ :=
  (1/2 : ℝ) * (f (k 0) + f (k 1) - f (k 2) - f (k 3))

theorem fullDifference_ae (R : ℝ) (f : H R) :
    fullDifference R f =ᵐ[pairingMeasure R] rawDifference f := by
  let a := pullback R 0 f
  let b := pullback R 1 f
  let c := pullback R 2 f
  let d := pullback R 3 f
  have h0 := pullback_ae R 0 f
  have h1 := pullback_ae R 1 f
  have h2 := pullback_ae R 2 f
  have h3 := pullback_ae R 3 f
  have ha := Lp.coeFn_add a b
  have hb := Lp.coeFn_sub (a+b) c
  have hc := Lp.coeFn_sub (a+b-c) d
  have hd := Lp.coeFn_smul (1/2 : ℝ) (a+b-c-d)
  change ((1/2 : ℝ) • (a+b-c-d) : J R) =ᵐ[pairingMeasure R] rawDifference f
  filter_upwards [h0, h1, h2, h3, ha, hb, hc, hd] with k hk0 hk1 hk2 hk3 hka hkb hkc hkd
  simp only [Pi.sub_apply, Pi.add_apply] at hka hkb hkc hkd
  rw [hkd]
  change (1/2 : ℝ) * ((a+b-c-d) k) = rawDifference f k
  rw [hkc, hkb, hka]
  change (1/2 : ℝ) * ((pullback R 0 f) k + (pullback R 1 f) k -
    (pullback R 2 f) k - (pullback R 3 f) k) = rawDifference f k
  rw [hk0, hk1, hk2, hk3]
  rfl

theorem fullDifference_bound (R : ℝ) (f : H R) : ‖fullDifference R f‖ ≤ 2 * ‖f‖ := by
  change ‖(1/2 : ℝ) • (pullback R 0 f + pullback R 1 f - pullback R 2 f - pullback R 3 f)‖ ≤ _
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0:ℝ)<1/2)]
  have h0 := norm_add_le (pullback R 0 f) (pullback R 1 f)
  have h1 := norm_sub_le (pullback R 0 f + pullback R 1 f) (pullback R 2 f)
  have h2 := norm_sub_le (pullback R 0 f + pullback R 1 f - pullback R 2 f) (pullback R 3 f)
  simp only [LinearIsometry.norm_map] at h0 h1 h2
  linarith

def fullOperator (R : ℝ) : H R →L[ℝ] H R :=
  (fullDifference R).adjoint.comp (fullDifference R)

theorem fullOperator_pairing (R : ℝ) (f g : H R) :
    inner ℝ f (fullOperator R g) = inner ℝ (fullDifference R f) (fullDifference R g) := by
  exact ContinuousLinearMap.adjoint_inner_right (fullDifference R) f (fullDifference R g)

theorem fullOperator_nonneg (R : ℝ) (f : H R) : 0 ≤ inner ℝ f (fullOperator R f) := by
  rw [fullOperator_pairing, real_inner_self_eq_norm_sq]
  positivity

theorem fullOperator_kernel (R : ℝ) : (fullOperator R).ker = (fullDifference R).ker :=
  ContinuousLinearMap.ker_adjoint_comp_self (fullDifference R)

theorem fullOperator_symmetric (R : ℝ) (f g : H R) :
    inner ℝ f (fullOperator R g) = inner ℝ (fullOperator R f) g := by
  calc
    _ = inner ℝ (fullDifference R f) (fullDifference R g) := fullOperator_pairing R f g
    _ = inner ℝ (fullDifference R g) (fullDifference R f) := real_inner_comm _ _
    _ = inner ℝ g (fullOperator R f) := (fullOperator_pairing R g f).symm
    _ = _ := real_inner_comm _ _

theorem fullOperator_integral (R : ℝ) (f g : H R) :
    inner ℝ f (fullOperator R g) =
      ∫ k, rawDifference f k * rawDifference g k ∂pairingMeasure R := by
  rw [fullOperator_pairing, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [fullDifference_ae R f, fullDifference_ae R g] with k hkf hkg
  rw [hkf, hkg]
  change rawDifference g k * rawDifference f k = rawDifference f k * rawDifference g k
  ring


theorem fullOperator_selfAdjoint (R : ℝ) : IsSelfAdjoint (fullOperator R) := by
  apply ContinuousLinearMap.isSelfAdjoint_iff'.mpr
  simp [fullOperator, ContinuousLinearMap.adjoint_comp]

theorem full_form_integrable (R : ℝ) (f g : H R) :
    Integrable (fun k => rawDifference f k * rawDifference g k) (pairingMeasure R) := by
  apply (L2.integrable_inner (fullDifference R f) (fullDifference R g)).congr
  filter_upwards [fullDifference_ae R f, fullDifference_ae R g] with k hkf hkg
  rw [hkf, hkg]
  change rawDifference g k * rawDifference f k = rawDifference f k * rawDifference g k
  ring


/-- The kernel is exactly the complete four-leg relation on the same joint
measure. This theorem does not assert a classification of that relation. -/
theorem fullOperator_eq_zero_iff (R : ℝ) (f : H R) :
    fullOperator R f = 0 ↔
      ∀ᵐ k ∂pairingMeasure R, f (k 0) + f (k 1) = f (k 2) + f (k 3) := by
  have hker : fullOperator R f = 0 ↔ fullDifference R f = 0 := by
    change f ∈ (fullOperator R).ker ↔ f ∈ (fullDifference R).ker
    rw [fullOperator_kernel]
  rw [hker]
  constructor
  · intro hf
    have ha := fullDifference_ae R f
    rw [hf] at ha
    filter_upwards [ha, Lp.coeFn_zero ℝ 2 (pairingMeasure R)] with k hk hz
    have hr : rawDifference f k = 0 := by simpa using hk.symm.trans hz
    dsimp [rawDifference] at hr
    linarith
  · intro hf
    apply Lp.ext
    filter_upwards [fullDifference_ae R f, hf, Lp.coeFn_zero ℝ 2 (pairingMeasure R)] with k hk hr hz
    rw [hk, hz]
    dsimp [rawDifference]
    linarith

theorem fullOperator_quadratic_eq_zero_iff (R : ℝ) (f : H R) :
    inner ℝ f (fullOperator R f) = 0 ↔
      ∀ᵐ k ∂pairingMeasure R, f (k 0) + f (k 1) = f (k 2) + f (k 3) := by
  rw [fullOperator_pairing, real_inner_self_eq_norm_sq]
  have hzero : ‖fullDifference R f‖ ^ 2 = 0 ↔ fullDifference R f = 0 := by
    rw [sq_eq_zero_iff, norm_eq_zero]
  rw [hzero]
  have hker : fullDifference R f = 0 ↔ fullOperator R f = 0 := by
    change f ∈ (fullDifference R).ker ↔ f ∈ (fullOperator R).ker
    rw [fullOperator_kernel]
  rw [hker, fullOperator_eq_zero_iff]

end
end Resonance.CollisionForm
