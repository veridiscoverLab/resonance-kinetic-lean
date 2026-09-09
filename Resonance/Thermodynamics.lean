import Resonance.Entropy
import Resonance.OnsagerPolynomial

/-!
The actual five-moment Rayleigh--Jeans map on the three-dimensional sharp cube.
All measures and basis functions come from Resonance.Entropy.
The positive Gram matrix and strict monotonicity below are proved from these
objects; they are not assumptions on an abstract matrix.
-/

open MeasureTheory
open scoped BigOperators

namespace Resonance.Thermodynamics

open Resonance.Entropy

abbrev Momentum := Fin 3 → ℝ
abbrev Parameter := Fin 5 → ℝ

def positiveDomain (R : ℝ) : Set Parameter :=
  {θ | ∀ k ∈ sharpCube R, 0 < denominator fiveInvariants θ k}

noncomputable def momentMap (R : ℝ) (θ : Parameter) : Parameter :=
  moment (cubeMeasure R) fiveInvariants (rj fiveInvariants θ)

noncomputable def gramMatrix (R : ℝ) (θ : Parameter) : Matrix (Fin 5) (Fin 5) ℝ :=
  fun i j => ∫ k, (rj fiveInvariants θ k)^2 * fiveInvariants i k * fiveInvariants j k
    ∂cubeMeasure R

theorem sharpCube_eq_polynomial_cube (R : ℝ) :
    sharpCube R = Resonance.OnsagerPolynomial.cube R := by
  ext k
  constructor
  · intro hk i _
    exact ⟨hk.1 i, hk.2 i⟩
  · intro hk
    exact ⟨fun i => (hk i (Set.mem_univ i)).1, fun i => (hk i (Set.mem_univ i)).2⟩

noncomputable def momentPolynomial (b : Parameter) : Resonance.OnsagerPolynomial.P :=
  Resonance.OnsagerPolynomial.invariant (b 0) (b 4) ![b 1, b 2, b 3]

theorem eval_momentPolynomial (b : Parameter) (k : Momentum) :
    MvPolynomial.eval k (momentPolynomial b) = denominator fiveInvariants b k := by
  simp [momentPolynomial, Resonance.OnsagerPolynomial.invariant,
    Resonance.OnsagerPolynomial.linear, Resonance.OnsagerPolynomial.radiusSq,
    denominator, fiveInvariants, Fin.sum_univ_succ]
  ring

/-- The original five polynomial moments are linearly independent modulo a.e.
equality on every cube of strictly positive radius. -/
theorem five_moment_ae_independent (R : ℝ) (hR : 0 < R) (b : Parameter)
    (hb : (fun k => denominator fiveInvariants b k) =ᵐ[cubeMeasure R] 0) :
    b = 0 := by
  have he : (fun k => MvPolynomial.eval k (momentPolynomial b))
      =ᵐ[volume.restrict (Resonance.OnsagerPolynomial.cube R)]
        (fun k => MvPolynomial.eval k (0 : Resonance.OnsagerPolynomial.P)) := by
    rw [← sharpCube_eq_polynomial_cube R]
    filter_upwards [hb] with k hk
    simpa only [eval_momentPolynomial, map_zero] using hk
  have hp := Resonance.OnsagerPolynomial.polynomial_eq_of_cube_ae R hR
    (momentPolynomial b) 0 he
  have hall (k : Momentum) : denominator fiveInvariants b k = 0 := by
    rw [← eval_momentPolynomial, hp, map_zero]
  have h0 := hall (fun _ => 0)
  have h1 := hall (fun i => if i = 0 then 1 else 0)
  have hm1 := hall (fun i => if i = 0 then -1 else 0)
  have h2 := hall (fun i => if i = 1 then 1 else 0)
  have h3 := hall (fun i => if i = 2 then 1 else 0)
  have h20 : (2 : Fin 3) ≠ 0 := by decide
  have h21 : (2 : Fin 3) ≠ 1 := by decide
  norm_num [denominator, fiveInvariants, Fin.sum_univ_succ, Matrix.cons_val,
    h20, h21, Ne.symm h20, Ne.symm h21] at h0 h1 hm1 h2 h3
  change b 0 + (b 1 + b 4) = 0 at h1
  change b 0 + (-b 1 + b 4) = 0 at hm1
  change b 0 + (b 2 + b 4) = 0 at h2
  change b 0 + (b 3 + b 4) = 0 at h3
  funext i
  fin_cases i <;> dsimp <;> linarith

theorem denominator_sub (θ β : Parameter) (k : Momentum) :
    denominator fiveInvariants (θ - β) k =
      denominator fiveInvariants θ k - denominator fiveInvariants β k := by
  simp only [denominator, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]

/-- Strict positivity of the integral follows from the actual polynomial
independence and a positive weight, with explicit integrability. -/
theorem weighted_square_integral_pos (R : ℝ) (hR : 0 < R)
    (b : Parameter) (hb : b ≠ 0) (w : Momentum → ℝ)
    (hw : ∀ᵐ k ∂cubeMeasure R, 0 < w k)
    (hi : Integrable (fun k => w k * (denominator fiveInvariants b k)^2)
      (cubeMeasure R)) :
    0 < ∫ k, w k * (denominator fiveInvariants b k)^2 ∂cubeMeasure R := by
  have hn : ∀ᵐ k ∂cubeMeasure R, 0 ≤ w k * (denominator fiveInvariants b k)^2 := by
    filter_upwards [hw] with k hkw
    exact mul_nonneg hkw.le (sq_nonneg _)
  have hnonneg := integral_nonneg_of_ae hn
  by_contra hnot
  have hz : (∫ k, w k * (denominator fiveInvariants b k)^2 ∂cubeMeasure R) = 0 :=
    le_antisymm (le_of_not_gt hnot) hnonneg
  have hae := (integral_eq_zero_iff_of_nonneg_ae hn hi).mp hz
  apply hb
  apply five_moment_ae_independent R hR b
  filter_upwards [hae, hw] with k hk hkw
  have hsq : (denominator fiveInvariants b k)^2 = 0 :=
    (mul_eq_zero.mp hk).resolve_left (ne_of_gt hkw)
  exact sq_eq_zero_iff.mp hsq

theorem gram_integrand_integrable (R : ℝ) (θ : Parameter)
    (hθ : θ ∈ positiveDomain R) (i j : Fin 5) :
    Integrable (fun k => (rj fiveInvariants θ k)^2 *
      fiveInvariants i k * fiveInvariants j k) (cubeMeasure R) :=
  ((((cube_rj_continuousOn R θ hθ).pow 2).mul
    (fiveInvariants_continuous i).continuousOn).mul
      (fiveInvariants_continuous j).continuousOn).integrableOn_Icc

theorem gram_square_integrable (R : ℝ) (θ b : Parameter)
    (hθ : θ ∈ positiveDomain R) :
    Integrable (fun k => (rj fiveInvariants θ k)^2 *
      (denominator fiveInvariants b k)^2) (cubeMeasure R) :=
  (((cube_rj_continuousOn R θ hθ).pow 2).mul
    ((cube_denominator_continuous b).continuousOn.pow 2)).integrableOn_Icc

/-- Strict positivity of the manuscript's full weighted Gram quadratic form. -/
theorem gram_quadratic_pos (R : ℝ) (hR : 0 < R) (θ : Parameter)
    (hθ : θ ∈ positiveDomain R) (b : Parameter) (hb : b ≠ 0) :
    0 < ∫ k, (rj fiveInvariants θ k)^2 *
      (denominator fiveInvariants b k)^2 ∂cubeMeasure R := by
  apply weighted_square_integral_pos R hR b hb
  · filter_upwards [cube_denominator_pos_ae R θ hθ] with k hk
    exact sq_pos_of_pos (inv_pos.mpr hk)
  · exact gram_square_integrable R θ b hθ


theorem gramMatrix_isHermitian (R : ℝ) (θ : Parameter) :
    (gramMatrix R θ).IsHermitian := by
  ext i j
  change (∫ k, (rj fiveInvariants θ k)^2 * fiveInvariants j k *
      fiveInvariants i k ∂cubeMeasure R) =
    ∫ k, (rj fiveInvariants θ k)^2 * fiveInvariants i k *
      fiveInvariants j k ∂cubeMeasure R
  apply integral_congr_ae
  filter_upwards [] with k
  ring

theorem gram_quadratic_identity (R : ℝ) (θ : Parameter)
    (hθ : θ ∈ positiveDomain R) (b : Parameter) :
    b ⬝ᵥ (gramMatrix R θ).mulVec b =
      ∫ k, (rj fiveInvariants θ k)^2 *
        (denominator fiveInvariants b k)^2 ∂cubeMeasure R := by
  classical
  have hi (i j : Fin 5) : Integrable (fun k =>
      b i * ((rj fiveInvariants θ k)^2 * fiveInvariants i k *
        fiveInvariants j k) * b j) (cubeMeasure R) :=
    ((gram_integrand_integrable R θ hθ i j).const_mul (b i)).mul_const (b j)
  calc
    b ⬝ᵥ (gramMatrix R θ).mulVec b =
        ∑ i, ∑ j, ∫ k, b i * ((rj fiveInvariants θ k)^2 *
          fiveInvariants i k * fiveInvariants j k) * b j ∂cubeMeasure R := by
      simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      rw [integral_mul_const, integral_const_mul]
      simp only [gramMatrix]
      ring
    _ = ∫ k, ∑ i, ∑ j, b i * ((rj fiveInvariants θ k)^2 *
          fiveInvariants i k * fiveInvariants j k) * b j ∂cubeMeasure R := by
      rw [integral_finset_sum (f := fun i k => ∑ j, b i *
        ((rj fiveInvariants θ k)^2 * fiveInvariants i k * fiveInvariants j k) * b j)
        Finset.univ (fun i _ => integrable_finset_sum Finset.univ (fun j _ => hi i j))]
      apply Finset.sum_congr rfl
      intro i _
      rw [integral_finset_sum (f := fun j k => b i *
        ((rj fiveInvariants θ k)^2 * fiveInvariants i k * fiveInvariants j k) * b j)
        Finset.univ (fun j _ => hi i j)]
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [] with k
      simp only [denominator, pow_two, Finset.mul_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring

/-- The actual Gram matrix is positive definite, without a matrix-positivity
hypothesis.  Only the sharp-cube radius and the RJ denominator are assumed positive. -/
theorem gramMatrix_posDef (R : ℝ) (hR : 0 < R) (θ : Parameter)
    (hθ : θ ∈ positiveDomain R) : (gramMatrix R θ).PosDef := by
  rw [Matrix.posDef_iff_dotProduct_mulVec]
  refine ⟨gramMatrix_isHermitian R θ, ?_⟩
  intro b hb
  simpa only [star_trivial, gram_quadratic_identity R θ hθ b] using
    gram_quadratic_pos R hR θ hθ b hb

theorem monotonicity_integrand_integrable (R : ℝ) (θ β b : Parameter)
    (hθ : θ ∈ positiveDomain R) (hβ : β ∈ positiveDomain R) :
    Integrable (fun k => rj fiveInvariants θ k * rj fiveInvariants β k *
      (denominator fiveInvariants b k)^2) (cubeMeasure R) :=
  (((cube_rj_continuousOn R θ hθ).mul (cube_rj_continuousOn R β hβ)).mul
    ((cube_denominator_continuous b).continuousOn.pow 2)).integrableOn_Icc

/-- Exact strict-monotonicity identity, with the original five moments and measure. -/
theorem momentMap_monotonicity_identity (R : ℝ) (θ β : Parameter)
    (hθ : θ ∈ positiveDomain R) (hβ : β ∈ positiveDomain R) :
    (θ - β) ⬝ᵥ (momentMap R θ - momentMap R β) =
      -(∫ k, rj fiveInvariants θ k * rj fiveInvariants β k *
        (denominator fiveInvariants (θ - β) k)^2 ∂cubeMeasure R) := by
  have hc := integral_cross (μ := cubeMeasure R) fiveInvariants β θ
    (cube_rj_moment_integrable R θ hθ) (cube_rj_moment_integrable R β hβ)
  change (∫ k, (rj fiveInvariants θ k - rj fiveInvariants β k) *
    ((rj fiveInvariants θ k)⁻¹ - (rj fiveInvariants β k)⁻¹) ∂cubeMeasure R) =
      (θ - β) ⬝ᵥ (momentMap R θ - momentMap R β) at hc
  rw [← hc, ← integral_neg]
  apply integral_congr_ae
  filter_upwards [cube_denominator_pos_ae R θ hθ, cube_denominator_pos_ae R β hβ]
    with k hkθ hkβ
  rw [denominator_sub]
  simp only [rj, inv_inv]
  field_simp [ne_of_gt hkθ, ne_of_gt hkβ]
  ring

theorem momentMap_strict_antimonotone (R : ℝ) (hR : 0 < R) (θ β : Parameter)
    (hθ : θ ∈ positiveDomain R) (hβ : β ∈ positiveDomain R) (hne : θ ≠ β) :
    (θ - β) ⬝ᵥ (momentMap R θ - momentMap R β) < 0 := by
  rw [momentMap_monotonicity_identity R θ β hθ hβ, neg_lt_zero]
  apply weighted_square_integral_pos R hR (θ - β) (sub_ne_zero.mpr hne)
    (fun k => rj fiveInvariants θ k * rj fiveInvariants β k)
  · filter_upwards [cube_denominator_pos_ae R θ hθ, cube_denominator_pos_ae R β hβ]
      with k hkθ hkβ
    exact mul_pos (inv_pos.mpr hkθ) (inv_pos.mpr hkβ)
  · exact monotonicity_integrand_integrable R θ β (θ - β) hθ hβ

/-- Genuine injectivity of the moment-matching map on the full positive RJ domain. -/
theorem momentMap_injective (R : ℝ) (hR : 0 < R) :
    Set.InjOn (momentMap R) (positiveDomain R) := by
  intro θ hθ β hβ heq
  by_contra hne
  have hs := momentMap_strict_antimonotone R hR θ β hθ hβ hne
  rw [heq, sub_self, dotProduct_zero] at hs
  exact (lt_irrefl 0 hs)


theorem denominator_joint_continuous :
    Continuous (fun p : Parameter × Momentum => denominator fiveInvariants p.1 p.2) := by
  unfold denominator
  exact continuous_finset_sum _ (fun i _ =>
    ((continuous_apply i).comp continuous_fst).mul
      ((fiveInvariants_continuous i).comp continuous_snd))

theorem positiveDomain_isOpen (R : ℝ) : IsOpen (positiveDomain R) := by
  rw [isOpen_iff_mem_nhds]
  intro θ hθ
  exact (isCompact_Icc : IsCompact (sharpCube R)).eventually_forall_of_forall_eventually
    (fun k hk => (denominator_joint_continuous.continuousAt).eventually
      (lt_mem_nhds (hθ k hk)))

theorem positiveDomain_convex (R : ℝ) : Convex ℝ (positiveDomain R) := by
  intro θ hθ β hβ a b ha hb hab k hk
  change 0 < ∑ i, (a * θ i + b * β i) * fiveInvariants i k
  simp only [add_mul, Finset.sum_add_distrib, mul_assoc, ← Finset.mul_sum]
  change 0 < a * denominator fiveInvariants θ k + b * denominator fiveInvariants β k
  have hpθ := hθ k hk
  have hpβ := hβ k hk
  rcases eq_or_lt_of_le ha with hza | hpa
  · have hb1 : b = 1 := by linarith
    rw [← hza, hb1]
    simpa using hpβ
  · exact add_pos_of_pos_of_nonneg (mul_pos hpa hpθ) (mul_nonneg hb hpβ.le)

noncomputable def denominatorCLM (k : Momentum) : Parameter →L[ℝ] ℝ :=
  ∑ i, fiveInvariants i k • ContinuousLinearMap.proj i

theorem denominatorCLM_apply (k : Momentum) (b : Parameter) :
    denominatorCLM k b = denominator fiveInvariants b k := by
  simp only [denominatorCLM, ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.proj_apply, smul_eq_mul, denominator]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem denominatorCLM_continuous : Continuous denominatorCLM := by
  unfold denominatorCLM
  exact continuous_finset_sum _ (fun i _ =>
    (fiveInvariants_continuous i).smul continuous_const)

noncomputable def integrandDerivative (i : Fin 5) (θ : Parameter) (k : Momentum) :
    Parameter →L[ℝ] ℝ :=
  (-(fiveInvariants i k * (rj fiveInvariants θ k)^2)) • denominatorCLM k

theorem integrand_hasFDerivAt (i : Fin 5) (θ : Parameter) (k : Momentum)
    (hk : denominator fiveInvariants θ k ≠ 0) :
    HasFDerivAt (fun β => fiveInvariants i k * rj fiveInvariants β k)
      (integrandDerivative i θ k) θ := by
  have hd : HasFDerivAt (fun β => denominator fiveInvariants β k)
      (denominatorCLM k) θ := by
    convert (denominatorCLM k).hasFDerivAt (x := θ) using 1
    funext β
    exact (denominatorCLM_apply k β).symm
  have hinv := (hasFDerivAt_inv hk).comp θ hd
  have h := hinv.const_mul (fiveInvariants i k)
  convert h using 1
  ext b
  simp [integrandDerivative, rj]
  ring


theorem integrandDerivative_continuousOn (R : ℝ) (i : Fin 5) :
    ContinuousOn (fun p : Parameter × Momentum => integrandDerivative i p.1 p.2)
      (positiveDomain R ×ˢ sharpCube R) := by
  have hc : ContinuousOn (fun p : Parameter × Momentum => rj fiveInvariants p.1 p.2)
      (positiveDomain R ×ˢ sharpCube R) :=
    denominator_joint_continuous.continuousOn.inv₀
      (fun p hp => ne_of_gt (hp.1 p.2 hp.2))
  exact ((((fiveInvariants_continuous i).comp continuous_snd).continuousOn.mul
    (hc.pow 2)).neg).smul
      (denominatorCLM_continuous.comp continuous_snd).continuousOn

theorem integrandDerivative_fixed_continuousOn (R : ℝ) (i : Fin 5)
    (θ : Parameter) (hθ : θ ∈ positiveDomain R) :
    ContinuousOn (integrandDerivative i θ) (sharpCube R) := by
  exact (((fiveInvariants_continuous i).continuousOn.mul
    ((cube_rj_continuousOn R θ hθ).pow 2)).neg).smul
      denominatorCLM_continuous.continuousOn

theorem moment_coordinate_hasFDerivAt (R : ℝ) (i : Fin 5) (θ : Parameter)
    (hθ : θ ∈ positiveDomain R) :
    HasFDerivAt (fun β => momentMap R β i)
      (∫ k, integrandDerivative i θ k ∂cubeMeasure R) θ := by
  letI := cube_finite R
  obtain ⟨r, hr, hsub⟩ := Metric.mem_nhds_iff.mp ((positiveDomain_isOpen R).mem_nhds hθ)
  have hr2 : 0 < r / 2 := half_pos hr
  have hclosed : Metric.closedBall θ (r / 2) ⊆ positiveDomain R := by
    intro β hβ
    exact hsub (Metric.mem_ball.mpr
      (lt_of_le_of_lt (Metric.mem_closedBall.mp hβ) (half_lt_self hr)))
  have hc := (integrandDerivative_continuousOn R i).mono
    (Set.prod_mono hclosed (Set.Subset.refl _))
  obtain ⟨C, hC⟩ := ((isCompact_closedBall θ (r / 2)).prod
    (isCompact_Icc : IsCompact (sharpCube R))).bddAbove_image hc.norm
  apply hasFDerivAt_integral_of_dominated_of_fderiv_le
    (s := Metric.closedBall θ (r / 2)) (bound := fun _ => C)
    (F' := fun β k => integrandDerivative i β k) (Metric.closedBall_mem_nhds θ hr2)
  · filter_upwards [(positiveDomain_isOpen R).eventually_mem hθ] with β hβ
    exact (((fiveInvariants_continuous i).continuousOn.mul
      (cube_rj_continuousOn R β hβ)).aestronglyMeasurable measurableSet_Icc)
  · exact cube_rj_moment_integrable R θ hθ i
  · exact (integrandDerivative_fixed_continuousOn R i θ hθ).aestronglyMeasurable
      measurableSet_Icc
  · filter_upwards [ae_restrict_mem (μ := volume) (s := sharpCube R) measurableSet_Icc]
      with k hk
    intro β hβ
    exact hC ⟨(β, k), ⟨hβ, hk⟩, rfl⟩
  · exact integrable_const C
  · filter_upwards [ae_restrict_mem (μ := volume) (s := sharpCube R) measurableSet_Icc]
      with k hk
    intro β hβ
    exact integrand_hasFDerivAt i β k (ne_of_gt (hclosed hβ k hk))

noncomputable def momentDerivative (R : ℝ) (θ : Parameter) : Parameter →L[ℝ] Parameter :=
  ContinuousLinearMap.pi (fun i => ∫ k, integrandDerivative i θ k ∂cubeMeasure R)

/-- Actual Fréchet differentiability of the five-moment map. -/
theorem momentMap_hasFDerivAt (R : ℝ) (θ : Parameter)
    (hθ : θ ∈ positiveDomain R) :
    HasFDerivAt (momentMap R) (momentDerivative R θ) θ := by
  exact hasFDerivAt_pi.mpr (fun i => moment_coordinate_hasFDerivAt R i θ hθ)


theorem momentDerivative_apply (R : ℝ) (θ : Parameter)
    (hθ : θ ∈ positiveDomain R) (b : Parameter) :
    momentDerivative R θ b = -(gramMatrix R θ).mulVec b := by
  classical
  funext i
  change (∫ k, integrandDerivative i θ k ∂cubeMeasure R) b =
    -((gramMatrix R θ).mulVec b i)
  have hdi : Integrable (integrandDerivative i θ) (cubeMeasure R) :=
    (integrandDerivative_fixed_continuousOn R i θ hθ).integrableOn_Icc
  rw [ContinuousLinearMap.integral_apply hdi]
  calc
    (∫ k, integrandDerivative i θ k b ∂cubeMeasure R) =
        ∫ k, -(∑ j, ((rj fiveInvariants θ k)^2 *
          fiveInvariants i k * fiveInvariants j k) * b j) ∂cubeMeasure R := by
      apply integral_congr_ae
      filter_upwards [] with k
      simp only [integrandDerivative, ContinuousLinearMap.smul_apply, smul_eq_mul,
        denominatorCLM_apply, denominator, Finset.mul_sum, ← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ = -((gramMatrix R θ).mulVec b i) := by
      rw [integral_neg, integral_finset_sum (f := fun j k =>
        ((rj fiveInvariants θ k)^2 * fiveInvariants i k * fiveInvariants j k) * b j)
        Finset.univ (fun j _ => (gram_integrand_integrable R θ hθ i j).mul_const (b j))]
      simp only [gramMatrix, Matrix.mulVec, dotProduct, integral_mul_const]

/-- The manuscript identity DU = -M for the actual five-moment integral. -/
theorem fderiv_momentMap_apply (R : ℝ) (θ : Parameter)
    (hθ : θ ∈ positiveDomain R) (b : Parameter) :
    fderiv ℝ (momentMap R) θ b = -(gramMatrix R θ).mulVec b := by
  rw [(momentMap_hasFDerivAt R θ hθ).fderiv]
  exact momentDerivative_apply R θ hθ b

theorem momentMap_differentiableOn (R : ℝ) :
    DifferentiableOn ℝ (momentMap R) (positiveDomain R) :=
  fun θ hθ => (momentMap_hasFDerivAt R θ hθ).differentiableAt.differentiableWithinAt

/-- The differential has no nonzero null vector; this is not an assumed rank condition. -/
theorem momentDerivative_injective (R : ℝ) (hR : 0 < R) (θ : Parameter)
    (hθ : θ ∈ positiveDomain R) : Function.Injective (momentDerivative R θ) := by
  apply (momentDerivative R θ).ker_eq_bot.mp
  rw [LinearMap.ker_eq_bot']
  intro b hb
  by_contra hne
  have hz : (gramMatrix R θ).mulVec b = 0 := by
    have he : -(gramMatrix R θ).mulVec b = 0 :=
      (momentDerivative_apply R θ hθ b).symm.trans hb
    exact neg_eq_zero.mp he
  have hpos := gram_quadratic_pos R hR θ hθ b hne
  rw [← gram_quadratic_identity R θ hθ b, hz, dotProduct_zero] at hpos
  exact lt_irrefl 0 hpos


theorem moment_coordinate_derivative_continuousAt (R : ℝ) (i : Fin 5) (θ : Parameter)
    (hθ : θ ∈ positiveDomain R) :
    ContinuousAt (fun β => ∫ k, integrandDerivative i β k ∂cubeMeasure R) θ := by
  letI := cube_finite R
  obtain ⟨r, hr, hsub⟩ := Metric.mem_nhds_iff.mp ((positiveDomain_isOpen R).mem_nhds hθ)
  have hr2 : 0 < r / 2 := half_pos hr
  have hclosed : Metric.closedBall θ (r / 2) ⊆ positiveDomain R := by
    intro β hβ
    exact hsub (Metric.mem_ball.mpr
      (lt_of_le_of_lt (Metric.mem_closedBall.mp hβ) (half_lt_self hr)))
  have hc := (integrandDerivative_continuousOn R i).mono
    (Set.prod_mono hclosed (Set.Subset.refl _))
  obtain ⟨C, hC⟩ := ((isCompact_closedBall θ (r / 2)).prod
    (isCompact_Icc : IsCompact (sharpCube R))).bddAbove_image hc.norm
  apply continuousAt_of_dominated (bound := fun _ => C)
  · filter_upwards [(positiveDomain_isOpen R).eventually_mem hθ] with β hβ
    exact (integrandDerivative_fixed_continuousOn R i β hβ).aestronglyMeasurable
      measurableSet_Icc
  · filter_upwards [Metric.closedBall_mem_nhds θ hr2] with β hβ
    filter_upwards [ae_restrict_mem (μ := volume) (s := sharpCube R) measurableSet_Icc]
      with k hk
    exact hC ⟨(β, k), ⟨hβ, hk⟩, rfl⟩
  · exact integrable_const C
  · filter_upwards [cube_denominator_pos_ae R θ hθ] with k hk
    have hden : ContinuousAt (fun β => denominator fiveInvariants β k) θ := by
      have he : (fun β => denominator fiveInvariants β k) = denominatorCLM k :=
        funext (fun β => (denominatorCLM_apply k β).symm)
      rw [he]
      exact (denominatorCLM k).continuous.continuousAt
    exact ((continuousAt_const.mul ((hden.inv₀ (ne_of_gt hk)).pow 2)).neg).smul
      continuousAt_const

noncomputable def bundleDerivative :
    (Fin 5 → Parameter →L[ℝ] ℝ) →ₗ[ℝ] (Parameter →L[ℝ] Parameter) where
  toFun := ContinuousLinearMap.pi
  map_add' x y := by ext b i; rfl
  map_smul' a x := by ext b i; rfl

theorem momentDerivative_continuousAt (R : ℝ) (θ : Parameter)
    (hθ : θ ∈ positiveDomain R) :
    ContinuousAt (momentDerivative R) θ := by
  exact bundleDerivative.continuous_of_finiteDimensional.continuousAt.comp
    (continuousAt_pi.mpr (fun i => moment_coordinate_derivative_continuousAt R i θ hθ))

/-- C¹ regularity on the full positive domain, with no differentiability input. -/
theorem momentMap_contDiffOn_one (R : ℝ) :
    ContDiffOn ℝ 1 (momentMap R) (positiveDomain R) := by
  rw [show (1 : WithTop ℕ∞) = 0 + 1 by simp,
    contDiffOn_succ_iff_fderiv_of_isOpen (positiveDomain_isOpen R)]
  refine ⟨momentMap_differentiableOn R, ?_, ?_⟩
  · intro h
    cases h
  · rw [contDiffOn_zero]
    intro θ hθ
    have he : fderiv ℝ (momentMap R) =ᶠ[nhds θ] momentDerivative R := by
      filter_upwards [(positiveDomain_isOpen R).eventually_mem hθ] with β hβ
      exact (momentMap_hasFDerivAt R β hβ).fderiv
    exact ((momentDerivative_continuousAt R θ hθ).congr he.symm).continuousWithinAt

end Resonance.Thermodynamics






