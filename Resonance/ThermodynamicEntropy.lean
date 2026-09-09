import Resonance.ThermodynamicChart

/-!
First and second Fréchet derivatives of the actual integral thermodynamic
potentials.  Both potentials below are defined by the manuscript's logarithmic
integrals.  Their derivative identities are consequences, not definitions.
The moment-coordinate statements are restricted to the actual open moment image.
-/

open MeasureTheory
open scoped BigOperators

namespace Resonance.ThermodynamicEntropy

open Resonance.Entropy Resonance.Thermodynamics Resonance.ThermodynamicChart

noncomputable def parameterPotential (R : ℝ) (θ : Parameter) : ℝ :=
  -(∫ k, Real.log (denominator fiveInvariants θ k) ∂cubeMeasure R)

noncomputable def matchedEntropy (R : ℝ) (hR : 0 < R) (U : Parameter) : ℝ :=
  -(∫ k, Real.log (rj fiveInvariants (momentInverse R hR U) k) ∂cubeMeasure R)

/-- The Euclidean pairing, as a continuous linear map into covectors. -/
noncomputable def covectorMap : Parameter →L[ℝ] (Parameter →L[ℝ] ℝ) :=
  ∑ i : Fin 5, (ContinuousLinearMap.proj i).smulRight (ContinuousLinearMap.proj i)

theorem covectorMap_apply (a b : Parameter) : covectorMap a b = a ⬝ᵥ b := by
  simp only [covectorMap, ContinuousLinearMap.sum_apply, ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.proj_apply, ContinuousLinearMap.smul_apply, smul_eq_mul, dotProduct]

noncomputable def potentialIntegrandDerivative (θ : Parameter) (k : Momentum) :
    Parameter →L[ℝ] ℝ :=
  (-rj fiveInvariants θ k) • denominatorCLM k

theorem negative_log_hasFDerivAt (θ : Parameter) (k : Momentum)
    (hk : denominator fiveInvariants θ k ≠ 0) :
    HasFDerivAt (fun β => -Real.log (denominator fiveInvariants β k))
      (potentialIntegrandDerivative θ k) θ := by
  have hd : HasFDerivAt (fun β => denominator fiveInvariants β k)
      (denominatorCLM k) θ := by
    convert (denominatorCLM k).hasFDerivAt (x := θ) using 1
    funext β
    exact (denominatorCLM_apply k β).symm
  convert ((Real.hasDerivAt_log hk).comp_hasFDerivAt θ hd).neg using 1
  ext b
  simp [potentialIntegrandDerivative, rj]

theorem potentialIntegrandDerivative_continuousOn (R : ℝ) :
    ContinuousOn (fun p : Parameter × Momentum => potentialIntegrandDerivative p.1 p.2)
      (positiveDomain R ×ˢ sharpCube R) := by
  have hc : ContinuousOn (fun p : Parameter × Momentum => rj fiveInvariants p.1 p.2)
      (positiveDomain R ×ˢ sharpCube R) :=
    denominator_joint_continuous.continuousOn.inv₀
      (fun p hp => ne_of_gt (hp.1 p.2 hp.2))
  exact hc.neg.smul (denominatorCLM_continuous.comp continuous_snd).continuousOn

theorem potentialIntegrandDerivative_fixed_continuousOn (R : ℝ) (θ : Parameter)
    (hθ : θ ∈ positiveDomain R) :
    ContinuousOn (potentialIntegrandDerivative θ) (sharpCube R) :=
  (cube_rj_continuousOn R θ hθ).neg.smul denominatorCLM_continuous.continuousOn

theorem cube_log_denominator_integrable (R : ℝ) (θ : Parameter)
    (hθ : θ ∈ positiveDomain R) :
    Integrable (fun k => Real.log (denominator fiveInvariants θ k)) (cubeMeasure R) :=
  ((cube_denominator_continuous θ).continuousOn.log
    (fun k hk => ne_of_gt (hθ k hk))).integrableOn_Icc

/-- Differentiation of the genuine logarithmic integral.  Uniform domination is
derived on a compact parameter ball times the original sharp cube. -/
theorem parameterPotential_hasFDerivAt_integral (R : ℝ) (θ : Parameter)
    (hθ : θ ∈ positiveDomain R) :
    HasFDerivAt (parameterPotential R)
      (∫ k, potentialIntegrandDerivative θ k ∂cubeMeasure R) θ := by
  letI := cube_finite R
  obtain ⟨r, hr, hsub⟩ := Metric.mem_nhds_iff.mp ((positiveDomain_isOpen R).mem_nhds hθ)
  have hr2 : 0 < r / 2 := half_pos hr
  have hclosed : Metric.closedBall θ (r / 2) ⊆ positiveDomain R := by
    intro β hβ
    exact hsub (Metric.mem_ball.mpr
      (lt_of_le_of_lt (Metric.mem_closedBall.mp hβ) (half_lt_self hr)))
  have hc := (potentialIntegrandDerivative_continuousOn R).mono
    (Set.prod_mono hclosed (Set.Subset.refl _))
  obtain ⟨C, hC⟩ := ((isCompact_closedBall θ (r / 2)).prod
    (isCompact_Icc : IsCompact (sharpCube R))).bddAbove_image hc.norm
  have hp : parameterPotential R = fun β =>
      ∫ k, -Real.log (denominator fiveInvariants β k) ∂cubeMeasure R := by
    funext β
    simp only [parameterPotential, integral_neg]
  rw [hp]
  apply hasFDerivAt_integral_of_dominated_of_fderiv_le
    (s := Metric.closedBall θ (r / 2)) (bound := fun _ => C)
    (F' := potentialIntegrandDerivative) (Metric.closedBall_mem_nhds θ hr2)
  · filter_upwards [(positiveDomain_isOpen R).eventually_mem hθ] with β hβ
    exact (((cube_denominator_continuous β).continuousOn.log
      (fun k hk => ne_of_gt (hβ k hk))).neg).aestronglyMeasurable measurableSet_Icc
  · exact (cube_log_denominator_integrable R θ hθ).neg
  · exact (potentialIntegrandDerivative_fixed_continuousOn R θ hθ).aestronglyMeasurable
      measurableSet_Icc
  · filter_upwards [ae_restrict_mem (μ := volume) (s := sharpCube R) measurableSet_Icc]
      with k hk
    intro β hβ
    exact hC ⟨(β, k), ⟨hβ, hk⟩, rfl⟩
  · exact integrable_const C
  · filter_upwards [ae_restrict_mem (μ := volume) (s := sharpCube R) measurableSet_Icc]
      with k hk
    intro β hβ
    exact negative_log_hasFDerivAt β k (ne_of_gt (hclosed hβ k hk))

theorem potential_derivative_integral (R : ℝ) (θ : Parameter)
    (hθ : θ ∈ positiveDomain R) :
    (∫ k, potentialIntegrandDerivative θ k ∂cubeMeasure R) =
      -covectorMap (momentMap R θ) := by
  ext b
  have hi : Integrable (potentialIntegrandDerivative θ) (cubeMeasure R) :=
    (potentialIntegrandDerivative_fixed_continuousOn R θ hθ).integrableOn_Icc
  rw [ContinuousLinearMap.integral_apply hi]
  calc
    (∫ k, potentialIntegrandDerivative θ k b ∂cubeMeasure R) =
        ∫ k, -(∑ i, (fiveInvariants i k * rj fiveInvariants θ k) * b i)
          ∂cubeMeasure R := by
      apply integral_congr_ae
      filter_upwards [] with k
      simp only [potentialIntegrandDerivative, ContinuousLinearMap.smul_apply, smul_eq_mul,
        denominatorCLM_apply, denominator, Finset.mul_sum, ← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = _ := by
      rw [integral_neg, integral_finset_sum (f := fun i k =>
        (fiveInvariants i k * rj fiveInvariants θ k) * b i)
        Finset.univ (fun i _ => (cube_rj_moment_integrable R θ hθ i).mul_const (b i))]
      simp only [ContinuousLinearMap.neg_apply, covectorMap_apply, dotProduct,
        momentMap, moment, integral_mul_const]

/-- DP(θ) = -U(θ), as equality of actual Fréchet derivatives. -/
theorem parameterPotential_hasFDerivAt (R : ℝ) (θ : Parameter)
    (hθ : θ ∈ positiveDomain R) :
    HasFDerivAt (parameterPotential R) (-covectorMap (momentMap R θ)) θ := by
  rw [← potential_derivative_integral R θ hθ]
  exact parameterPotential_hasFDerivAt_integral R θ hθ

theorem parameterPotential_fderiv (R : ℝ) (θ : Parameter)
    (hθ : θ ∈ positiveDomain R) :
    fderiv ℝ (parameterPotential R) θ = -covectorMap (momentMap R θ) :=
  (parameterPotential_hasFDerivAt R θ hθ).fderiv

noncomputable def potentialHessian (R : ℝ) (θ : Parameter) :
    Parameter →L[ℝ] (Parameter →L[ℝ] ℝ) :=
  -(covectorMap.comp (momentDerivative R θ))

/-- Second Fréchet differentiation is taken after the first derivative of the
integral has been proved; it is not a formal Hessian assigned to P. -/
theorem parameterPotential_second_hasFDerivAt (R : ℝ) (θ : Parameter)
    (hθ : θ ∈ positiveDomain R) :
    HasFDerivAt (fderiv ℝ (parameterPotential R)) (potentialHessian R θ) θ := by
  have hd := (covectorMap.hasFDerivAt.comp θ (momentMap_hasFDerivAt R θ hθ)).neg
  apply hd.congr_of_eventuallyEq
  filter_upwards [(positiveDomain_isOpen R).eventually_mem hθ] with β hβ
  exact parameterPotential_fderiv R β hβ

theorem potentialHessian_apply (R : ℝ) (θ : Parameter)
    (hθ : θ ∈ positiveDomain R) (a b : Parameter) :
    potentialHessian R θ a b = ((gramMatrix R θ).mulVec a) ⬝ᵥ b := by
  simp only [potentialHessian, ContinuousLinearMap.neg_apply, ContinuousLinearMap.comp_apply,
    covectorMap_apply, momentDerivative_apply R θ hθ a, neg_dotProduct, neg_neg]

theorem parameterPotential_second_fderiv (R : ℝ) (θ : Parameter)
    (hθ : θ ∈ positiveDomain R) (a b : Parameter) :
    fderiv ℝ (fderiv ℝ (parameterPotential R)) θ a b =
      ((gramMatrix R θ).mulVec a) ⬝ᵥ b := by
  rw [(parameterPotential_second_hasFDerivAt R θ hθ).fderiv]
  exact potentialHessian_apply R θ hθ a b


theorem gram_entry_symm (R : ℝ) (θ : Parameter) (i j : Fin 5) :
    gramMatrix R θ i j = gramMatrix R θ j i := by
  apply integral_congr_ae
  filter_upwards [] with k
  ring

theorem gram_bilinear_symm (R : ℝ) (θ a b : Parameter) :
    ((gramMatrix R θ).mulVec a) ⬝ᵥ b = a ⬝ᵥ (gramMatrix R θ).mulVec b := by
  simp only [Matrix.mulVec, dotProduct, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [gram_entry_symm R θ j i]
  ring

/-- M(θ) θ = U(θ) follows from N² q = N in the original integrals. -/
theorem gram_mul_parameter (R : ℝ) (θ : Parameter)
    (hθ : θ ∈ positiveDomain R) :
    (gramMatrix R θ).mulVec θ = momentMap R θ := by
  classical
  funext i
  change (∑ j, gramMatrix R θ i j * θ j) =
    ∫ k, fiveInvariants i k * rj fiveInvariants θ k ∂cubeMeasure R
  calc
    (∑ j, gramMatrix R θ i j * θ j) =
        ∫ k, ∑ j, ((rj fiveInvariants θ k)^2 * fiveInvariants i k *
          fiveInvariants j k) * θ j ∂cubeMeasure R := by
      rw [integral_finset_sum (f := fun j k =>
        ((rj fiveInvariants θ k)^2 * fiveInvariants i k * fiveInvariants j k) * θ j)
        Finset.univ (fun j _ => (gram_integrand_integrable R θ hθ i j).mul_const (θ j))]
      simp only [gramMatrix, integral_mul_const]
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [cube_denominator_pos_ae R θ hθ] with k hk
      have he : (∑ j, ((rj fiveInvariants θ k)^2 * fiveInvariants i k *
          fiveInvariants j k) * θ j) =
          (rj fiveInvariants θ k)^2 * fiveInvariants i k *
            denominator fiveInvariants θ k := by
        simp only [denominator, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        ring
      rw [he]
      simp only [rj]
      field_simp [ne_of_gt hk]

/-- This identity is derived from the two logarithmic integral definitions. -/
theorem matchedEntropy_eq_neg_potential (R : ℝ) (hR : 0 < R) (U : Parameter) :
    matchedEntropy R hR U = -parameterPotential R (momentInverse R hR U) := by
  simp only [matchedEntropy, parameterPotential, rj, Real.log_inv, integral_neg, neg_neg]

theorem inverse_derivative_covector (R : ℝ) (hR : 0 < R) (U : Parameter)
    (hU : U ∈ momentImage R) :
    (covectorMap (momentMap R (momentInverse R hR U))).comp
      ((derivativeEquiv R hR (momentInverse R hR U)
        (momentInverse_mem R hR U hU)).symm : Parameter →L[ℝ] Parameter) =
      -covectorMap (momentInverse R hR U) := by
  ext b
  change covectorMap (momentMap R (momentInverse R hR U))
      ((derivativeEquiv R hR (momentInverse R hR U)
        (momentInverse_mem R hR U hU)).symm b) =
      -covectorMap (momentInverse R hR U) b
  rw [covectorMap_apply, covectorMap_apply,
    ← gram_mul_parameter R (momentInverse R hR U) (momentInverse_mem R hR U hU),
    gram_bilinear_symm]
  have hg := momentInverse_fderiv_gram R hR U hU b
  rw [(momentInverse_hasFDerivAt R hR U hU).fderiv] at hg
  change (gramMatrix R (momentInverse R hR U)).mulVec
    ((derivativeEquiv R hR (momentInverse R hR U)
      (momentInverse_mem R hR U hU)).symm b) = -b at hg
  rw [hg, dotProduct_neg]

/-- DE(U) = -θ(U) for the actual logarithmic entropy, not a formal Legendre definition. -/
theorem matchedEntropy_hasFDerivAt (R : ℝ) (hR : 0 < R) (U : Parameter)
    (hU : U ∈ momentImage R) :
    HasFDerivAt (matchedEntropy R hR) (-covectorMap (momentInverse R hR U)) U := by
  have hp := (parameterPotential_hasFDerivAt R (momentInverse R hR U)
    (momentInverse_mem R hR U hU)).neg
  have hc := hp.comp U (momentInverse_hasFDerivAt R hR U hU)
  simp only [neg_neg] at hc
  rw [inverse_derivative_covector R hR U hU] at hc
  convert hc using 1
  funext V
  exact matchedEntropy_eq_neg_potential R hR V

theorem matchedEntropy_fderiv (R : ℝ) (hR : 0 < R) (U : Parameter)
    (hU : U ∈ momentImage R) :
    fderiv ℝ (matchedEntropy R hR) U = -covectorMap (momentInverse R hR U) :=
  (matchedEntropy_hasFDerivAt R hR U hU).fderiv

noncomputable def entropyHessian (R : ℝ) (hR : 0 < R) (U : Parameter) :
    Parameter →L[ℝ] (Parameter →L[ℝ] ℝ) :=
  -(covectorMap.comp (fderiv ℝ (momentInverse R hR) U))

theorem matchedEntropy_second_hasFDerivAt (R : ℝ) (hR : 0 < R) (U : Parameter)
    (hU : U ∈ momentImage R) :
    HasFDerivAt (fderiv ℝ (matchedEntropy R hR)) (entropyHessian R hR U) U := by
  have hd := (covectorMap.hasFDerivAt.comp U
    (momentInverse_hasFDerivAt R hR U hU)).neg
  rw [← (momentInverse_hasFDerivAt R hR U hU).fderiv] at hd
  apply hd.congr_of_eventuallyEq
  filter_upwards [(momentImage_isOpen R hR).eventually_mem hU] with V hV
  exact matchedEntropy_fderiv R hR V hV

theorem matchedEntropy_second_fderiv (R : ℝ) (hR : 0 < R) (U : Parameter)
    (hU : U ∈ momentImage R) (a b : Parameter) :
    fderiv ℝ (fderiv ℝ (matchedEntropy R hR)) U a b =
      -(fderiv ℝ (momentInverse R hR) U a) ⬝ᵥ b := by
  rw [(matchedEntropy_second_hasFDerivAt R hR U hU).fderiv]
  simp only [entropyHessian, ContinuousLinearMap.neg_apply, ContinuousLinearMap.comp_apply,
    covectorMap_apply, neg_dotProduct]

/-- The Hessian is M⁻¹: its representing vector is the unique solution of Mv=a.
The equation uses the original integral Gram matrix without an assumed inverse. -/
theorem entropyHessian_inverse_gram (R : ℝ) (hR : 0 < R) (U : Parameter)
    (hU : U ∈ momentImage R) (a : Parameter) :
    (gramMatrix R (momentInverse R hR U)).mulVec
      (-(fderiv ℝ (momentInverse R hR) U a)) = a := by
  rw [Matrix.mulVec_neg, momentInverse_fderiv_gram R hR U hU a, neg_neg]


theorem parameterPotential_contDiffOn_two (R : ℝ) :
    ContDiffOn ℝ 2 (parameterPotential R) (positiveDomain R) := by
  rw [show (2 : WithTop ℕ∞) = 1 + 1 by norm_num,
    contDiffOn_succ_iff_fderiv_of_isOpen (positiveDomain_isOpen R)]
  refine ⟨fun θ hθ =>
    (parameterPotential_hasFDerivAt R θ hθ).differentiableAt.differentiableWithinAt, ?_, ?_⟩
  · intro h
    cases h
  · exact (covectorMap.contDiff.comp_contDiffOn (momentMap_contDiffOn_one R)).neg.congr
      (fun θ hθ => parameterPotential_fderiv R θ hθ)

theorem matchedEntropy_contDiffOn_two (R : ℝ) (hR : 0 < R) :
    ContDiffOn ℝ 2 (matchedEntropy R hR) (momentImage R) := by
  rw [show (2 : WithTop ℕ∞) = 1 + 1 by norm_num,
    contDiffOn_succ_iff_fderiv_of_isOpen (momentImage_isOpen R hR)]
  refine ⟨fun U hU =>
    (matchedEntropy_hasFDerivAt R hR U hU).differentiableAt.differentiableWithinAt, ?_, ?_⟩
  · intro h
    cases h
  · exact (covectorMap.contDiff.comp_contDiffOn (momentInverse_contDiffOn R hR)).neg.congr
      (fun U hU => matchedEntropy_fderiv R hR U hU)

theorem parameterPotential_hessian_positive (R : ℝ) (hR : 0 < R)
    (θ : Parameter) (hθ : θ ∈ positiveDomain R) (a : Parameter) (ha : a ≠ 0) :
    0 < fderiv ℝ (fderiv ℝ (parameterPotential R)) θ a a := by
  rw [parameterPotential_second_fderiv R θ hθ a a, dotProduct_comm,
    gram_quadratic_identity R θ hθ a]
  exact gram_quadratic_pos R hR θ hθ a ha

theorem matchedEntropy_hessian_positive (R : ℝ) (hR : 0 < R) (U : Parameter)
    (hU : U ∈ momentImage R) (a : Parameter) (ha : a ≠ 0) :
    0 < fderiv ℝ (fderiv ℝ (matchedEntropy R hR)) U a a := by
  let v : Parameter := -(fderiv ℝ (momentInverse R hR) U a)
  have hMv : (gramMatrix R (momentInverse R hR U)).mulVec v = a :=
    entropyHessian_inverse_gram R hR U hU a
  have hv : v ≠ 0 := by
    intro hv0
    apply ha
    rw [hv0, Matrix.mulVec_zero] at hMv
    exact hMv.symm
  rw [matchedEntropy_second_fderiv R hR U hU a a]
  change 0 < v ⬝ᵥ a
  rw [← hMv, gram_quadratic_identity R (momentInverse R hR U)
    (momentInverse_mem R hR U hU) v]
  exact gram_quadratic_pos R hR (momentInverse R hR U)
    (momentInverse_mem R hR U hU) v hv

end Resonance.ThermodynamicEntropy


