import Resonance.ThermodynamicChart

/-!
Higher regularity and exact parameter jets of the actual sharp-cube moment map.
The power-integral family is differentiated under the same cube measure, with
compact domination at every positive parameter. No PDE solution or uniform
nonlinear energy estimate is an assumption or a conclusion of this module.
-/

open MeasureTheory
open scoped BigOperators ContDiff

namespace Resonance.ThermodynamicJets

open Resonance.Entropy Resonance.Thermodynamics Resonance.ThermodynamicChart

noncomputable def powerIntegral (R : ℝ) (m : ℕ) (w : Momentum → ℝ)
    (θ : Parameter) : ℝ :=
  ∫ k, w k * (rj fiveInvariants θ k) ^ (m + 1) ∂cubeMeasure R

noncomputable def powerIntegrandDerivative (m : ℕ) (w : Momentum → ℝ)
    (θ : Parameter) (k : Momentum) : Parameter →L[ℝ] ℝ :=
  (-((m + 1 : ℕ) : ℝ) * w k * (rj fiveInvariants θ k) ^ (m + 2)) • denominatorCLM k

theorem power_integrand_hasFDerivAt (m : ℕ) (w : Momentum → ℝ)
    (θ : Parameter) (k : Momentum) (hk : denominator fiveInvariants θ k ≠ 0) :
    HasFDerivAt (fun β => w k * (rj fiveInvariants β k) ^ (m + 1))
      (powerIntegrandDerivative m w θ k) θ := by
  have hd : HasFDerivAt (fun β => denominator fiveInvariants β k)
      (denominatorCLM k) θ := by
    convert (denominatorCLM k).hasFDerivAt (x := θ) using 1
    exact funext (fun β => (denominatorCLM_apply k β).symm)
  have hi := (hasFDerivAt_inv hk).comp θ hd
  have hp := (hi.pow (m + 1)).const_mul (w k)
  convert hp using 1
  ext b
  simp [powerIntegrandDerivative, rj, pow_succ]
  ring

theorem power_integrandDerivative_continuousOn (R : ℝ) (m : ℕ)
    (w : Momentum → ℝ) (hw : Continuous w) :
    ContinuousOn (fun p : Parameter × Momentum => powerIntegrandDerivative m w p.1 p.2)
      (positiveDomain R ×ˢ sharpCube R) := by
  have hc : ContinuousOn (fun p : Parameter × Momentum => rj fiveInvariants p.1 p.2)
      (positiveDomain R ×ˢ sharpCube R) :=
    denominator_joint_continuous.continuousOn.inv₀
      (fun p hp => ne_of_gt (hp.1 p.2 hp.2))
  exact ((continuousOn_const.mul (hw.comp continuous_snd).continuousOn).mul
    (hc.pow (m + 2))).smul (denominatorCLM_continuous.comp continuous_snd).continuousOn

theorem power_integrandDerivative_fixed_continuousOn (R : ℝ) (m : ℕ)
    (w : Momentum → ℝ) (hw : Continuous w) (θ : Parameter)
    (hθ : θ ∈ positiveDomain R) :
    ContinuousOn (powerIntegrandDerivative m w θ) (sharpCube R) :=
  ((continuousOn_const.mul hw.continuousOn).mul
    ((cube_rj_continuousOn R θ hθ).pow (m + 2))).smul
      denominatorCLM_continuous.continuousOn

theorem power_integrable (R : ℝ) (m : ℕ) (w : Momentum → ℝ)
    (hw : Continuous w) (θ : Parameter) (hθ : θ ∈ positiveDomain R) :
    Integrable (fun k => w k * (rj fiveInvariants θ k) ^ (m + 1))
      (cubeMeasure R) :=
  (hw.continuousOn.mul ((cube_rj_continuousOn R θ hθ).pow (m + 1))).integrableOn_Icc

theorem powerIntegral_hasFDerivAt_integral (R : ℝ) (m : ℕ)
    (w : Momentum → ℝ) (hw : Continuous w) (θ : Parameter)
    (hθ : θ ∈ positiveDomain R) :
    HasFDerivAt (powerIntegral R m w)
      (∫ k, powerIntegrandDerivative m w θ k ∂cubeMeasure R) θ := by
  letI := cube_finite R
  obtain ⟨r, hr, hsub⟩ := Metric.mem_nhds_iff.mp ((positiveDomain_isOpen R).mem_nhds hθ)
  have hr2 : 0 < r / 2 := half_pos hr
  have hclosed : Metric.closedBall θ (r / 2) ⊆ positiveDomain R := by
    intro β hβ
    exact hsub (Metric.mem_ball.mpr
      (lt_of_le_of_lt (Metric.mem_closedBall.mp hβ) (half_lt_self hr)))
  have hc := (power_integrandDerivative_continuousOn R m w hw).mono
    (Set.prod_mono hclosed (Set.Subset.refl _))
  obtain ⟨C, hC⟩ := ((isCompact_closedBall θ (r / 2)).prod
    (isCompact_Icc : IsCompact (sharpCube R))).bddAbove_image hc.norm
  apply hasFDerivAt_integral_of_dominated_of_fderiv_le
    (s := Metric.closedBall θ (r / 2)) (bound := fun _ => C)
    (F' := fun β k => powerIntegrandDerivative m w β k) (Metric.closedBall_mem_nhds θ hr2)
  · filter_upwards [(positiveDomain_isOpen R).eventually_mem hθ] with β hβ
    exact (hw.continuousOn.mul ((cube_rj_continuousOn R β hβ).pow (m + 1))).aestronglyMeasurable
      measurableSet_Icc
  · exact power_integrable R m w hw θ hθ
  · exact (power_integrandDerivative_fixed_continuousOn R m w hw θ hθ).aestronglyMeasurable
      measurableSet_Icc
  · filter_upwards [ae_restrict_mem (μ := volume) (s := sharpCube R) measurableSet_Icc]
      with k hk
    intro β hβ
    exact hC ⟨(β, k), ⟨hβ, hk⟩, rfl⟩
  · exact integrable_const C
  · filter_upwards [ae_restrict_mem (μ := volume) (s := sharpCube R) measurableSet_Icc]
      with k hk
    intro β hβ
    exact power_integrand_hasFDerivAt m w β k (ne_of_gt (hclosed hβ k hk))

noncomputable def powerDerivative (R : ℝ) (m : ℕ) (w : Momentum → ℝ)
    (θ : Parameter) : Parameter →L[ℝ] ℝ :=
  ∑ j, (-((m + 1 : ℕ) : ℝ) *
    powerIntegral R (m + 1) (fun k => w k * fiveInvariants j k) θ) •
      ContinuousLinearMap.proj j

theorem power_derivative_integral (R : ℝ) (m : ℕ) (w : Momentum → ℝ)
    (hw : Continuous w) (θ : Parameter) (hθ : θ ∈ positiveDomain R) :
    (∫ k, powerIntegrandDerivative m w θ k ∂cubeMeasure R) =
      powerDerivative R m w θ := by
  ext b
  have hdi : Integrable (powerIntegrandDerivative m w θ) (cubeMeasure R) :=
    (power_integrandDerivative_fixed_continuousOn R m w hw θ hθ).integrableOn_Icc
  rw [ContinuousLinearMap.integral_apply hdi]
  calc
    (∫ k, powerIntegrandDerivative m w θ k b ∂cubeMeasure R) =
      ∫ k, ∑ j, -((m + 1 : ℕ) : ℝ) *
        ((w k * fiveInvariants j k) * (rj fiveInvariants θ k) ^ ((m + 1) + 1)) * b j
        ∂cubeMeasure R := by
      apply integral_congr_ae
      filter_upwards [] with k
      simp only [powerIntegrandDerivative, ContinuousLinearMap.smul_apply, smul_eq_mul,
        denominatorCLM_apply, denominator, Finset.mul_sum, Nat.add_assoc]
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ = powerDerivative R m w θ b := by
      rw [integral_finset_sum Finset.univ (fun j _ =>
        ((power_integrable R (m + 1) (fun k => w k * fiveInvariants j k)
          (hw.mul (fiveInvariants_continuous j)) θ hθ).const_mul _).mul_const _)]
      simp [powerDerivative, powerIntegral, integral_const_mul, integral_mul_const]

theorem powerIntegral_hasFDerivAt (R : ℝ) (m : ℕ) (w : Momentum → ℝ)
    (hw : Continuous w) (θ : Parameter) (hθ : θ ∈ positiveDomain R) :
    HasFDerivAt (powerIntegral R m w) (powerDerivative R m w θ) θ := by
  rw [← power_derivative_integral R m w hw θ hθ]
  exact powerIntegral_hasFDerivAt_integral R m w hw θ hθ

theorem powerIntegral_contDiffOn_finite (R : ℝ) (n : ℕ) :
    ∀ (m : ℕ) (w : Momentum → ℝ), Continuous w →
      ContDiffOn ℝ n (powerIntegral R m w) (positiveDomain R) := by
  induction n with
  | zero =>
    intro m w hw
    change ContDiffOn ℝ (0 : WithTop ℕ∞) (powerIntegral R m w) (positiveDomain R)
    rw [contDiffOn_zero]
    intro θ hθ
    exact (powerIntegral_hasFDerivAt R m w hw θ hθ).continuousAt.continuousWithinAt
  | succ n ih =>
    intro m w hw
    rw [show ((n + 1 : ℕ) : WithTop ℕ∞) = (n : WithTop ℕ∞) + 1 by simp,
      contDiffOn_succ_iff_fderiv_of_isOpen (positiveDomain_isOpen R)]
    refine ⟨?_, ?_, ?_⟩
    · intro θ hθ
      exact (powerIntegral_hasFDerivAt R m w hw θ hθ).differentiableAt.differentiableWithinAt
    · intro h
      simp at h
    · have hd : ContDiffOn ℝ n (powerDerivative R m w) (positiveDomain R) := by
        unfold powerDerivative
        exact ContDiffOn.sum (fun j _ =>
          (contDiffOn_const.mul (ih (m + 1) (fun k => w k * fiveInvariants j k)
            (hw.mul (fiveInvariants_continuous j)))).smul contDiffOn_const)
      exact hd.congr (fun θ hθ => (powerIntegral_hasFDerivAt R m w hw θ hθ).fderiv)

theorem momentMap_contDiffOn_finite (R : ℝ) (n : ℕ) :
    ContDiffOn ℝ n (momentMap R) (positiveDomain R) := by
  apply contDiffOn_pi.mpr
  intro i
  exact (powerIntegral_contDiffOn_finite R n 0 (fiveInvariants i)
    (fiveInvariants_continuous i)).congr (fun θ _ => by
      simp [powerIntegral, momentMap, moment])

theorem momentMap_contDiffAt_finite (R : ℝ) (n : ℕ) (θ : Parameter)
    (hθ : θ ∈ positiveDomain R) : ContDiffAt ℝ n (momentMap R) θ :=
  (momentMap_contDiffOn_finite R n).contDiffAt ((positiveDomain_isOpen R).mem_nhds hθ)

theorem momentInverse_contDiffAt_finite (R : ℝ) (hR : 0 < R) (n : ℕ) (U : Parameter)
    (hU : U ∈ momentImage R) : ContDiffAt ℝ n (momentInverse R hR) U :=
  (momentChart R hR).contDiffAt_symm hU
    (momentMap_hasFDerivAt_equiv R hR (momentInverse R hR U)
      (momentInverse_mem R hR U hU))
    (momentMap_contDiffAt_finite R n (momentInverse R hR U)
      (momentInverse_mem R hR U hU))

theorem momentInverse_contDiffOn_finite (R : ℝ) (hR : 0 < R) (n : ℕ) :
    ContDiffOn ℝ n (momentInverse R hR) (momentImage R) :=
  fun U hU => (momentInverse_contDiffAt_finite R hR n U hU).contDiffWithinAt

theorem momentMap_contDiffOn_infty (R : ℝ) :
    ContDiffOn ℝ ∞ (momentMap R) (positiveDomain R) :=
  contDiffOn_infty.mpr (momentMap_contDiffOn_finite R)

theorem momentInverse_contDiffOn_infty (R : ℝ) (hR : 0 < R) :
    ContDiffOn ℝ ∞ (momentInverse R hR) (momentImage R) :=
  contDiffOn_infty.mpr (momentInverse_contDiffOn_finite R hR)

/-! Uniform finite-jet bounds on an actual compact positive parameter family.
No bounds on a kinetic solution or its time derivatives are assumed here. -/

theorem compact_finite_jet_bounds (f : Parameter → Parameter) (s : Set Parameter)
    (hs : IsOpen s) (hf : ContDiffOn ℝ ∞ f s) (K : Set Parameter)
    (hK : IsCompact K) (hKs : K ⊆ s) (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ x ∈ K, ∀ j : ℕ, j ≤ n →
      ‖iteratedFDeriv ℝ j f x‖ ≤ C := by
  have hbound (j : ℕ) : ∃ C : ℝ, ∀ x ∈ K, ‖iteratedFDeriv ℝ j f x‖ ≤ C := by
    exact hK.exists_bound_of_continuousOn
      ((ContinuousOn.continuousOn_iteratedFDeriv (contDiffOn_infty.mp hf j)
        hs le_rfl).mono hKs)
  induction n with
  | zero =>
    obtain ⟨C, hC⟩ := hbound 0
    refine ⟨max C 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _), ?_⟩
    intro x hx j hj
    have hj0 : j = 0 := Nat.eq_zero_of_le_zero hj
    subst j
    exact (hC x hx).trans (le_max_left _ _)
  | succ n ih =>
    obtain ⟨C, hCpos, hC⟩ := ih
    obtain ⟨D, hD⟩ := hbound (n + 1)
    refine ⟨max C D, lt_of_lt_of_le hCpos (le_max_left _ _), ?_⟩
    intro x hx j hj
    rcases Nat.eq_or_lt_of_le hj with he | he
    · subst j
      exact (hD x hx).trans (le_max_right _ _)
    · exact (hC x hx j (Nat.le_of_lt_succ he)).trans (le_max_left _ _)

theorem moment_chart_compact_jet_bounds (R : ℝ) (hR : 0 < R)
    (K : Set Parameter) (hK : IsCompact K) (hKpos : K ⊆ positiveDomain R) (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ θ ∈ K, ∀ j : ℕ, j ≤ n →
      ‖iteratedFDeriv ℝ j (momentMap R) θ‖ ≤ C ∧
      ‖iteratedFDeriv ℝ j (momentInverse R hR) (momentMap R θ)‖ ≤ C := by
  obtain ⟨C, hCpos, hC⟩ := compact_finite_jet_bounds (momentMap R) (positiveDomain R)
    (positiveDomain_isOpen R) (momentMap_contDiffOn_infty R) K hK hKpos n
  have himage : IsCompact (momentMap R '' K) :=
    hK.image_of_continuousOn ((momentMap_contDiffOn_infty R).continuousOn.mono hKpos)
  have hsub : momentMap R '' K ⊆ momentImage R := by
    rintro U ⟨θ, hθ, rfl⟩
    exact ⟨θ, hKpos hθ, rfl⟩
  obtain ⟨D, hDpos, hD⟩ := compact_finite_jet_bounds (momentInverse R hR) (momentImage R)
    (momentImage_isOpen R hR) (momentInverse_contDiffOn_infty R hR)
    (momentMap R '' K) himage hsub n
  refine ⟨max C D, lt_of_lt_of_le hCpos (le_max_left _ _), ?_⟩
  intro θ hθ j hj
  exact ⟨(hC θ hθ j hj).trans (le_max_left _ _),
    (hD (momentMap R θ) ⟨θ, hθ, rfl⟩ j hj).trans (le_max_right _ _)⟩

theorem moment_chart_compact_third_jet_bounds (R : ℝ) (hR : 0 < R)
    (K : Set Parameter) (hK : IsCompact K) (hKpos : K ⊆ positiveDomain R) :
    ∃ C : ℝ, 0 < C ∧ ∀ θ ∈ K, ∀ j : ℕ, j ≤ 3 →
      ‖iteratedFDeriv ℝ j (momentMap R) θ‖ ≤ C ∧
      ‖iteratedFDeriv ℝ j (momentInverse R hR) (momentMap R θ)‖ ≤ C :=
  moment_chart_compact_jet_bounds R hR K hK hKpos 3

/-! Exact iterated directional jets. Directions are fixed parameter vectors;
the derivatives below are actual Fréchet derivatives, not formal tensors. -/

noncomputable def directional (a : Parameter) (f : Parameter → ℝ) (θ : Parameter) : ℝ :=
  fderiv ℝ f θ a

theorem powerIntegral_directional (R : ℝ) (m : ℕ) (w : Momentum → ℝ)
    (hw : Continuous w) (θ : Parameter) (hθ : θ ∈ positiveDomain R) (a : Parameter) :
    directional a (powerIntegral R m w) θ =
      -((m + 1 : ℕ) : ℝ) * powerIntegral R (m + 1)
        (fun k => w k * denominator fiveInvariants a k) θ := by
  unfold directional
  rw [(powerIntegral_hasFDerivAt_integral R m w hw θ hθ).fderiv]
  have hi : Integrable (powerIntegrandDerivative m w θ) (cubeMeasure R) :=
    (power_integrandDerivative_fixed_continuousOn R m w hw θ hθ).integrableOn_Icc
  rw [ContinuousLinearMap.integral_apply hi]
  unfold powerIntegral
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with k
  simp only [powerIntegrandDerivative, ContinuousLinearMap.smul_apply, smul_eq_mul,
    denominatorCLM_apply, Nat.add_assoc]
  ring

theorem directional_congr_near (R : ℝ) (f g : Parameter → ℝ)
    (h : ∀ θ ∈ positiveDomain R, f θ = g θ)
    (θ : Parameter) (hθ : θ ∈ positiveDomain R) (a : Parameter) :
    directional a f θ = directional a g θ := by
  have he : f =ᶠ[nhds θ] g := by
    filter_upwards [(positiveDomain_isOpen R).eventually_mem hθ] with β hβ
    exact h β hβ
  unfold directional
  rw [he.fderiv_eq]

theorem directional_const_mul_power (R : ℝ) (m : ℕ) (w : Momentum → ℝ)
    (hw : Continuous w) (θ : Parameter) (hθ : θ ∈ positiveDomain R)
    (a : Parameter) (s : ℝ) :
    directional a (fun β => s * powerIntegral R m w β) θ =
      s * directional a (powerIntegral R m w) θ := by
  unfold directional
  rw [((powerIntegral_hasFDerivAt R m w hw θ hθ).const_mul s).fderiv,
    (powerIntegral_hasFDerivAt R m w hw θ hθ).fderiv]
  rfl

theorem powerIntegral_directional_two (R : ℝ) (m : ℕ) (w : Momentum → ℝ)
    (hw : Continuous w) (θ : Parameter) (hθ : θ ∈ positiveDomain R) (a b : Parameter) :
    directional b (directional a (powerIntegral R m w)) θ =
      ((m + 1 : ℕ) : ℝ) * ((m + 2 : ℕ) : ℝ) * powerIntegral R (m + 2)
        (fun k => (w k * denominator fiveInvariants a k) *
          denominator fiveInvariants b k) θ := by
  rw [directional_congr_near R _ _ (fun β hβ =>
    powerIntegral_directional R m w hw β hβ a) θ hθ b]
  rw [directional_const_mul_power R (m + 1)
      (fun k => w k * denominator fiveInvariants a k)
      (hw.mul (cube_denominator_continuous a)) θ hθ b (-((m + 1 : ℕ) : ℝ)),
    powerIntegral_directional R (m + 1) (fun k => w k * denominator fiveInvariants a k)
      (hw.mul (cube_denominator_continuous a)) θ hθ b]
  simp only [Nat.add_assoc, Nat.cast_add, Nat.cast_one]
  ring

theorem powerIntegral_directional_three (R : ℝ) (m : ℕ) (w : Momentum → ℝ)
    (hw : Continuous w) (θ : Parameter) (hθ : θ ∈ positiveDomain R) (a b c : Parameter) :
    directional c (directional b (directional a (powerIntegral R m w))) θ =
      -(((m + 1 : ℕ) : ℝ) * ((m + 2 : ℕ) : ℝ) * ((m + 3 : ℕ) : ℝ)) *
        powerIntegral R (m + 3)
          (fun k => ((w k * denominator fiveInvariants a k) *
            denominator fiveInvariants b k) * denominator fiveInvariants c k) θ := by
  rw [directional_congr_near R _ _ (fun β hβ =>
    powerIntegral_directional_two R m w hw β hβ a b) θ hθ c]
  rw [directional_const_mul_power R (m + 2)
      (fun k => (w k * denominator fiveInvariants a k) * denominator fiveInvariants b k)
      ((hw.mul (cube_denominator_continuous a)).mul (cube_denominator_continuous b)) θ hθ c
      (((m + 1 : ℕ) : ℝ) * ((m + 2 : ℕ) : ℝ)),
    powerIntegral_directional R (m + 2)
      (fun k => (w k * denominator fiveInvariants a k) * denominator fiveInvariants b k)
      ((hw.mul (cube_denominator_continuous a)).mul (cube_denominator_continuous b)) θ hθ c]
  simp only [Nat.add_assoc, Nat.cast_add, Nat.cast_one]
  ring

theorem momentMap_directional_one (R : ℝ) (θ : Parameter)
    (hθ : θ ∈ positiveDomain R) (i : Fin 5) (a : Parameter) :
    directional a (fun β => momentMap R β i) θ =
      -(∫ k, (fiveInvariants i k * denominator fiveInvariants a k) *
        (rj fiveInvariants θ k) ^ 2 ∂cubeMeasure R) := by
  have he : (fun β => momentMap R β i) = powerIntegral R 0 (fiveInvariants i) := by
    funext β
    simp [momentMap, moment, powerIntegral]
  rw [he, powerIntegral_directional R 0 _ (fiveInvariants_continuous i) θ hθ a]
  norm_num [powerIntegral]

theorem momentMap_directional_two (R : ℝ) (θ : Parameter)
    (hθ : θ ∈ positiveDomain R) (i : Fin 5) (a b : Parameter) :
    directional b (directional a (fun β => momentMap R β i)) θ =
      2 * (∫ k, ((fiveInvariants i k * denominator fiveInvariants a k) *
        denominator fiveInvariants b k) *
        (rj fiveInvariants θ k) ^ 3 ∂cubeMeasure R) := by
  have he : (fun β => momentMap R β i) = powerIntegral R 0 (fiveInvariants i) := by
    funext β
    simp [momentMap, moment, powerIntegral]
  rw [he, powerIntegral_directional_two R 0 _ (fiveInvariants_continuous i) θ hθ a b]
  norm_num [powerIntegral]

theorem momentMap_directional_three (R : ℝ) (θ : Parameter)
    (hθ : θ ∈ positiveDomain R) (i : Fin 5) (a b c : Parameter) :
    directional c (directional b (directional a (fun β => momentMap R β i))) θ =
      -6 * (∫ k, (((fiveInvariants i k * denominator fiveInvariants a k) *
        denominator fiveInvariants b k) * denominator fiveInvariants c k) *
        (rj fiveInvariants θ k) ^ 4 ∂cubeMeasure R) := by
  have he : (fun β => momentMap R β i) = powerIntegral R 0 (fiveInvariants i) := by
    funext β
    simp [momentMap, moment, powerIntegral]
  rw [he, powerIntegral_directional_three R 0 _ (fiveInvariants_continuous i) θ hθ a b c]
  norm_num [powerIntegral]

end Resonance.ThermodynamicJets
