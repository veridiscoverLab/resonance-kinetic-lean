import Resonance.ActualCornerSpatialMoser

/-! The entire actual 2+1 derivative product, with small amplitude only
outside the original corner layer. The two legs are never independently
sampled, and their spatial derivative fields stay those of the same p. -/
open Set MeasureTheory Filter
open scoped Topology ENNReal
namespace Resonance.ActualTwoOneFullMoser
noncomputable section
open ResonantMeasure WeightedJointMeasure FrequencyWeightedForm
open FreeTransport SpatialChainRule SpatialJetSpace SpatialIntegrationByParts SpatialThirdGN
open SpatialMomentumSections SpatialProductGN CornerPairTruncation JointCornerHolder
open ActualCornerSpatialMoser
set_option maxHeartbeats 1800000

def mixedConstant (M N : ℝ) : ℝ:=(35640*M)^((2:ℝ)/3)*(2500*N^4)^((1:ℝ)/3)
def smallConstant (κ M : ℝ) : ℝ:=mixedConstant κ M+mixedConstant M κ

theorem mixedConstant_nonnegative {M N : ℝ} (hM : 0 ≤ M) : 0 ≤ mixedConstant M N := by
  unfold mixedConstant
  positivity

theorem actual_mixed_amplitude_spatial {R : ℝ} (p : JetSpace R) (k l : E)
    (i j n : Fin 3) {M N : ℝ} (hM : 0 ≤ M)
    (hk : amplitude p k ≤ M) (hl : amplitude p l ≤ N) :
    (∫X,(evaluate (secondCubeSection p i j) X k*evaluate (firstCubeSection p n) X l)^2) ≤
      mixedConstant M N*(mass p k)^((2:ℝ)/3)*(mass p l)^((1:ℝ)/3) := by
  let d:=zeroSection (secondCubeSection p i j) k
  let e:=zeroSection (firstCubeSection p n) l
  have h:=two_one_product_holder d e
  have hd : integralCLM ((absField d)^3) ≤35640*M*mass p k :=
    (ambient_coordinate_GN p k i j).2.trans
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hk (by norm_num))
        (mass_nonnegative p k))
  have he : integralCLM (e^6) ≤2500*N^4*mass p l :=
    (ambient_coordinate_GN p l n n).1.trans
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (norm_nonneg _) hl 4) (by norm_num)) (mass_nonnegative p l))
  have hdn : 0 ≤ integralCLM ((absField d)^3) :=
    integral_nonneg (fun X=>pow_nonneg (abs_nonneg (d X)) 3)
  have hb:=mul_le_mul
    (Real.rpow_le_rpow hdn hd (by norm_num : (0:ℝ)≤2/3))
    (Real.rpow_le_rpow (sixth_nonnegative e) he (by norm_num : (0:ℝ)≤1/3))
    (Real.rpow_nonneg (sixth_nonnegative e) _)
    (Real.rpow_nonneg (mul_nonneg (mul_nonneg (by norm_num) hM) (mass_nonnegative p k)) _)
  have hr : (35640*M*mass p k)^((2:ℝ)/3)*(2500*N^4*mass p l)^((1:ℝ)/3)=
      mixedConstant M N*(mass p k)^((2:ℝ)/3)*(mass p l)^((1:ℝ)/3) := by
    rw [Real.mul_rpow (by positivity : 0 ≤ 35640*M) (mass_nonnegative p k),
      Real.mul_rpow (by positivity : 0 ≤ 2500*N^4) (mass_nonnegative p l)]
    unfold mixedConstant
    ring
  exact h.trans (hb.trans_eq hr)

def massProduct {R : ℝ} (p : JetSpace R) (a b : Fin 4) (q : FourMomenta) : ℝ:=
  (mass p (q a))^((2:ℝ)/3)*(mass p (q b))^((1:ℝ)/3)

theorem massProduct_nonnegative {R : ℝ} (p : JetSpace R) (a b : Fin 4) (q : FourMomenta) :
    0 ≤ massProduct p a b q :=
  mul_nonneg (Real.rpow_nonneg (mass_nonnegative p _) _) (Real.rpow_nonneg (mass_nonnegative p _) _)

theorem actual_massProduct_data {R : ℝ} (hR : 0 ≤ R) {θ : Thermodynamics.Parameter}
    (hθ : θ∈Thermodynamics.positiveDomain R) (p : JetSpace R) (a b : Fin 4) :
    Integrable (massProduct p a b) (jointMeasure R θ) ∧
    (∫q,massProduct p a b q∂jointMeasure R θ) ≤ ∫k,mass p k∂marginal R θ := by
  letI:=actual_marginal_finite hR hθ
  have hma:=(all_legs_preserve R θ a).integrable_comp_of_integrable (mass_integrable p (marginal R θ))
  have hmb:=(all_legs_preserve R θ b).integrable_comp_of_integrable (mass_integrable p (marginal R θ))
  have h:=holder_two_one_data hma hmb (fun q=>mass_nonnegative p (q a)) (fun q=>mass_nonnegative p (q b))
  constructor
  · exact h.1
  · have hb:=h.2
    change (∫q,massProduct p a b q∂jointMeasure R θ) ≤
      (∫q,mass p (q a)∂jointMeasure R θ)^((2:ℝ)/3)*
        (∫q,mass p (q b)∂jointMeasure R θ)^((1:ℝ)/3) at hb
    rw [actual_leg_integral R θ a (mass_integrable p _),
      actual_leg_integral R θ b (mass_integrable p _),
      ←Real.rpow_add_of_nonneg (integral_nonneg (mass_nonnegative p)) (by norm_num) (by norm_num)] at hb
    norm_num at hb ⊢
    exact hb

def uncutPairSquare {R : ℝ} (f g : C(MomentumDomain R,ScalarField))
    (a b : Fin 4) (z : SpatialTorus×FourMomenta) : ℝ:=
  (evaluate f z.1 (z.2 a)*evaluate g z.1 (z.2 b))^2

theorem uncutPairSquare_integrable {R : ℝ} (hR : 0 ≤ R) {θ : Thermodynamics.Parameter}
    (hθ : θ∈Thermodynamics.positiveDomain R) (f g : C(MomentumDomain R,ScalarField))
    (a b : Fin 4) : Integrable (uncutPairSquare f g a b) (volume.prod (jointMeasure R θ)) := by
  letI:=jointMeasure_finite hR hθ
  have hmeas:=(leg_evaluate_measurable f a).mul (leg_evaluate_measurable g b)
  apply Integrable.of_bound (hmeas.pow_const 2).aestronglyMeasurable ((‖f‖*‖g‖)^2)
  apply ae_of_all
  intro z
  change ‖(evaluate f z.1 (z.2 a)*evaluate g z.1 (z.2 b))^2‖ ≤ (‖f‖*‖g‖)^2
  rw [Real.norm_eq_abs,abs_pow,abs_mul]
  exact pow_le_pow_left₀ (mul_nonneg (abs_nonneg _) (abs_nonneg _))
    (mul_le_mul (evaluate_bound f _ _) (evaluate_bound g _ _) (abs_nonneg _) (norm_nonneg f)) 2

theorem full_two_one_pointwise {R : ℝ} (p : JetSpace R) (a b : Fin 4)
    (i j n : Fin 3) (η : ℝ) {κ M : ℝ} (hκ : 0 ≤ κ) (hM : 0 ≤ M)
    (hp : ∀k,amplitude p k ≤ M) (hbulk : ∀k,cut R η k=0 → amplitude p k ≤ κ)
    (q : FourMomenta) :
    (∫X,(evaluate (secondCubeSection p i j) X (q a)*evaluate (firstCubeSection p n) X (q b))^2) ≤
      smallConstant κ M*massProduct p a b q+twoOneConstant M*cutMassProduct p a b η q := by
  have he : cutMassProduct p a b η q=massProduct p a b q*cut R η (q a)*cut R η (q b) :=
    cutMassProduct_identity p a b η q
  have hm:=massProduct_nonnegative p a b q
  have hleft:=mixedConstant_nonnegative (N:=M) hκ
  have hright:=mixedConstant_nonnegative (N:=κ) hM
  have hz : 0 ≤ smallConstant κ M := add_nonneg hleft hright
  rcases cut_zero_or_one R η (q a) with ha|ha
  · have h:=actual_mixed_amplitude_spatial p (q a) (q b) i j n hκ (hbulk _ ha) (hp _)
    rw [he,ha]
    simp only [mul_zero,zero_mul,add_zero]
    change _ ≤ (mixedConstant κ M+mixedConstant M κ)*massProduct p a b q
    simp only [mul_assoc] at h
    change _ ≤ mixedConstant κ M*massProduct p a b q at h
    nlinarith [mul_nonneg hright hm]
  · rcases cut_zero_or_one R η (q b) with hb|hb
    · have h:=actual_mixed_amplitude_spatial p (q a) (q b) i j n hM (hp _) (hbulk _ hb)
      rw [he,hb,mul_zero,mul_zero,add_zero]
      change _ ≤ (mixedConstant κ M+mixedConstant M κ)*massProduct p a b q
      simp only [mul_assoc] at h
      change _ ≤ mixedConstant M κ*massProduct p a b q at h
      nlinarith [mul_nonneg hleft hm]
    · have h:=actual_two_one_spatial p (q a) (q b) i j n hM (hp _) (hp _)
      rw [he,ha,hb,mul_one,mul_one]
      simp only [mul_assoc] at h
      change _ ≤ twoOneConstant M*massProduct p a b q at h
      exact h.trans (le_add_of_nonneg_left (mul_nonneg hz hm))

/-- The entire actual 2+1 allocation: bulk smallness and the original
corner-pair compactness are simultaneously paid in the same joint law. -/
theorem actual_full_two_one_moser {R : ℝ} (hR : 0 ≤ R) {θ : Thermodynamics.Parameter}
    (hθ : θ∈Thermodynamics.positiveDomain R) (p : JetSpace R) (a b : Fin 4)
    (hab : a≠b) (i j n : Fin 3) (η : ℝ) {κ M : ℝ} (hκ : 0 ≤ κ) (hM : 0 ≤ M)
    (hp : ∀k,amplitude p k ≤ M) (hbulk : ∀k,cut R η k=0 → amplitude p k ≤ κ) :
    (∫z,uncutPairSquare (secondCubeSection p i j) (firstCubeSection p n) a b z
      ∂volume.prod (jointMeasure R θ)) ≤
      (smallConstant κ M+twoOneConstant M*(omega R θ η)^((2:ℝ)/3))*(∫k,mass p k∂marginal R θ) := by
  letI:=jointMeasure_finite hR hθ
  rw [integral_prod_symm _ (uncutPairSquare_integrable hR hθ _ _ a b)]
  have hd:=actual_massProduct_data hR hθ p a b
  have hc:=actual_cutMassProduct_bound hR hθ p a b hab η
  have hi:=(hd.1.const_mul (smallConstant κ M)).add
    ((cutMassProduct_integrable hR hθ p a b η).const_mul (twoOneConstant M))
  have hm : (∫q,(∫X,(evaluate (secondCubeSection p i j) X (q a)*
      evaluate (firstCubeSection p n) X (q b))^2)∂jointMeasure R θ) ≤
      ∫q,smallConstant κ M*massProduct p a b q+twoOneConstant M*cutMassProduct p a b η q
        ∂jointMeasure R θ := by
    apply integral_mono_of_nonneg (ae_of_all _ (fun q=>integral_nonneg (fun X=>sq_nonneg _))) hi
    exact ae_of_all _ (full_two_one_pointwise p a b i j n η hκ hM hp hbulk)
  rw [integral_add (hd.1.const_mul _) ((cutMassProduct_integrable hR hθ p a b η).const_mul _),
    integral_const_mul,integral_const_mul] at hm
  have hz : 0 ≤ smallConstant κ M:=add_nonneg (mixedConstant_nonnegative hκ) (mixedConstant_nonnegative hM)
  have h1:=mul_le_mul_of_nonneg_left hd.2 hz
  have h2:=mul_le_mul_of_nonneg_left hc (twoOneConstant_nonneg hM)
  simp only [uncutPairSquare]
  nlinarith

theorem smallConstant_continuous (M : ℝ) : Continuous (fun κ:ℝ=>smallConstant κ M) := by
  unfold smallConstant mixedConstant
  apply Continuous.add
  · exact ((Real.continuous_rpow_const (by norm_num : (0:ℝ)≤2/3)).comp
      (continuous_const.mul continuous_id)).mul continuous_const
  · exact continuous_const.mul ((Real.continuous_rpow_const (by norm_num : (0:ℝ)≤1/3)).comp
      (continuous_const.mul (continuous_id.pow 4)))

theorem smallConstant_zero (M : ℝ) : smallConstant 0 M=0 := by
  norm_num [smallConstant,mixedConstant]

/-- Both bulk amplitude and the actual corner-pair norm tend to zero in
one joint limit. No rate for the geometric modulus is assumed. -/
theorem full_two_one_coefficient_tendsto {R : ℝ} (hR : 0<R) {θ : Thermodynamics.Parameter}
    (hθ : θ∈Thermodynamics.positiveDomain R) (M : ℝ) :
    Tendsto (fun z:ℝ×ℝ=>smallConstant z.1 M+twoOneConstant M*(omega R θ z.2)^((2:ℝ)/3))
      (𝓝 ((0:ℝ),(0:ℝ))) (𝓝 0) := by
  have hb : Tendsto (fun z:ℝ×ℝ=>smallConstant z.1 M) (𝓝 ((0:ℝ),(0:ℝ))) (𝓝 0) := by
    simpa only [Function.comp_def,smallConstant_zero] using
      ((smallConstant_continuous M).comp continuous_fst).tendsto ((0:ℝ),(0:ℝ))
  have hc : Tendsto (fun z:ℝ×ℝ=>(omega R θ z.2)^((2:ℝ)/3))
      (𝓝 ((0:ℝ),(0:ℝ))) (𝓝 0) := by
    have hw:=(omega_tendsto hR hθ).comp (continuous_snd.tendsto ((0:ℝ),(0:ℝ)))
    have hr:=((Real.continuous_rpow_const (by norm_num : (0:ℝ)≤2/3)).tendsto 0).comp hw
    norm_num at hr ⊢
    exact hr
  simpa only [mul_zero,add_zero] using hb.add (hc.const_mul (twoOneConstant M))

end
end Resonance.ActualTwoOneFullMoser
