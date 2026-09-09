import Resonance.ActualTwoOneFullMoser
import Mathlib.Analysis.MeanInequalities

/-! The entire 1+1+1 allocation under genuine bulk-only amplitude
smallness, still on the original common spatial/quartet measure. -/
open Set MeasureTheory Filter
open scoped Topology ENNReal
namespace Resonance.ActualThreeFullMoser
noncomputable section
open ResonantMeasure WeightedJointMeasure FrequencyWeightedForm
open FreeTransport SpatialChainRule SpatialJetSpace SpatialIntegrationByParts
open SpatialMomentumSections SpatialProductGN CornerPairTruncation JointCornerHolder
open ActualCornerSpatialMoser
set_option maxHeartbeats 1800000

def threeConstant (A B C : ℝ) : ℝ:=
  (2500*A^4)^((1:ℝ)/3)*(2500*B^4)^((1:ℝ)/3)*(2500*C^4)^((1:ℝ)/3)
def threeSmallConstant (κ M : ℝ) : ℝ:=
  threeConstant κ M M+threeConstant M κ M+threeConstant M M κ

theorem threeConstant_nonnegative (A B C : ℝ) : 0 ≤ threeConstant A B C := by
  unfold threeConstant
  positivity

theorem actual_three_amplitude_spatial {R : ℝ} (p : JetSpace R) (k l m : E)
    (i j n : Fin 3) {A B C : ℝ}
    (hk : amplitude p k ≤ A) (hl : amplitude p l ≤ B) (hm : amplitude p m ≤ C) :
    (∫X,(evaluate (firstCubeSection p i) X k*evaluate (firstCubeSection p j) X l*
      evaluate (firstCubeSection p n) X m)^2) ≤
      threeConstant A B C*(mass p k)^((1:ℝ)/3)*(mass p l)^((1:ℝ)/3)*(mass p m)^((1:ℝ)/3) := by
  let d:=zeroSection (firstCubeSection p i) k
  let e:=zeroSection (firstCubeSection p j) l
  let f:=zeroSection (firstCubeSection p n) m
  have hg (a:E) (b:Fin 3) (M:ℝ) (ha:amplitude p a ≤ M) :
      integralCLM ((zeroSection (firstCubeSection p b) a)^6) ≤2500*M^4*mass p a := by
    exact (ambient_coordinate_GN p a b b).1.trans
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (norm_nonneg _) ha 4) (by norm_num)) (mass_nonnegative p a))
  have h:=three_product_holder d e f
  have h1:=Real.rpow_le_rpow (sixth_nonnegative d) (hg k i A hk) (by norm_num : (0:ℝ)≤1/3)
  have h2:=Real.rpow_le_rpow (sixth_nonnegative e) (hg l j B hl) (by norm_num : (0:ℝ)≤1/3)
  have h3:=Real.rpow_le_rpow (sixth_nonnegative f) (hg m n C hm) (by norm_num : (0:ℝ)≤1/3)
  have hb:=mul_le_mul (mul_le_mul h1 h2 (Real.rpow_nonneg (sixth_nonnegative e) _)
    (Real.rpow_nonneg (mul_nonneg (by positivity) (mass_nonnegative p k)) _)) h3
    (Real.rpow_nonneg (sixth_nonnegative f) _)
    (mul_nonneg (Real.rpow_nonneg (mul_nonneg (by positivity) (mass_nonnegative p k)) _)
      (Real.rpow_nonneg (mul_nonneg (by positivity) (mass_nonnegative p l)) _))
  have hr : (2500*A^4*mass p k)^((1:ℝ)/3)*(2500*B^4*mass p l)^((1:ℝ)/3)*
      (2500*C^4*mass p m)^((1:ℝ)/3)=
      threeConstant A B C*(mass p k)^((1:ℝ)/3)*(mass p l)^((1:ℝ)/3)*(mass p m)^((1:ℝ)/3) := by
    rw [Real.mul_rpow (by positivity : 0 ≤ 2500*A^4) (mass_nonnegative p k),
      Real.mul_rpow (by positivity : 0 ≤ 2500*B^4) (mass_nonnegative p l),
      Real.mul_rpow (by positivity : 0 ≤ 2500*C^4) (mass_nonnegative p m)]
    unfold threeConstant
    ring
  exact h.trans (hb.trans_eq hr)

def massTriple {R : ℝ} (p : JetSpace R) (a b d : Fin 4) (q : FourMomenta) : ℝ:=
  (mass p (q a))^((1:ℝ)/3)*(mass p (q b))^((1:ℝ)/3)*(mass p (q d))^((1:ℝ)/3)

theorem massTriple_nonnegative {R : ℝ} (p : JetSpace R) (a b d : Fin 4) (q : FourMomenta) :
    0 ≤ massTriple p a b d q :=
  mul_nonneg (mul_nonneg (Real.rpow_nonneg (mass_nonnegative p _) _)
    (Real.rpow_nonneg (mass_nonnegative p _) _)) (Real.rpow_nonneg (mass_nonnegative p _) _)

theorem massTriple_measurable {R : ℝ} (p : JetSpace R) (a b d : Fin 4) :
    Measurable (massTriple p a b d) := by
  have h (i:Fin 4) : Measurable (fun q:FourMomenta=>(mass p (q i))^((1:ℝ)/3)) :=
    (Real.continuous_rpow_const (by norm_num : (0:ℝ)≤1/3)).measurable.comp
      ((mass_measurable p).comp (measurable_pi_apply i))
  exact ((h a).mul (h b)).mul (h d)

theorem massTriple_arithmetic {R : ℝ} (p : JetSpace R) (a b d : Fin 4) (q : FourMomenta) :
    massTriple p a b d q ≤ (1/3:ℝ)*mass p (q a)+(1/3:ℝ)*mass p (q b)+(1/3:ℝ)*mass p (q d) :=
  Real.geom_mean_le_arith_mean3_weighted (by norm_num) (by norm_num) (by norm_num)
    (mass_nonnegative p _) (mass_nonnegative p _) (mass_nonnegative p _) (by norm_num)

theorem actual_massTriple_data {R : ℝ} (hR : 0 ≤ R) {θ : Thermodynamics.Parameter}
    (hθ : θ∈Thermodynamics.positiveDomain R) (p : JetSpace R) (a b d : Fin 4) :
    Integrable (massTriple p a b d) (jointMeasure R θ) ∧
    (∫q,massTriple p a b d q∂jointMeasure R θ) ≤ ∫k,mass p k∂marginal R θ := by
  letI:=actual_marginal_finite hR hθ
  have hi (i:Fin 4) := (all_legs_preserve R θ i).integrable_comp_of_integrable
    (mass_integrable p (marginal R θ))
  have hr:=(((hi a).const_mul (1/3:ℝ)).add ((hi b).const_mul (1/3:ℝ))).add ((hi d).const_mul (1/3:ℝ))
  have hs : Integrable (massTriple p a b d) (jointMeasure R θ) := by
    apply hr.mono' (massTriple_measurable p a b d).aestronglyMeasurable
    apply ae_of_all
    intro q
    rw [Real.norm_eq_abs,abs_of_nonneg (massTriple_nonnegative p a b d q)]
    exact massTriple_arithmetic p a b d q
  constructor
  · exact hs
  · have hb:=integral_mono hs hr (massTriple_arithmetic p a b d)
    simp only [Pi.add_apply,Function.comp_def] at hb
    have hsum1:=integral_add ((hi a).const_mul (1/3:ℝ)) ((hi b).const_mul (1/3:ℝ))
    have hsum2:=integral_add (((hi a).const_mul (1/3:ℝ)).add ((hi b).const_mul (1/3:ℝ)))
      ((hi d).const_mul (1/3:ℝ))
    simp only [Pi.add_apply,Function.comp_def] at hsum1 hsum2
    rw [hsum1] at hsum2
    simp only [integral_const_mul] at hsum2
    rw [hsum2,
      actual_leg_integral R θ a (mass_integrable p _),actual_leg_integral R θ b (mass_integrable p _),
      actual_leg_integral R θ d (mass_integrable p _)] at hb
    linarith

def uncutTripleSquare {R : ℝ} (f g h : C(MomentumDomain R,ScalarField))
    (a b d : Fin 4) (z : SpatialTorus×FourMomenta) : ℝ:=
  (evaluate f z.1 (z.2 a)*evaluate g z.1 (z.2 b)*evaluate h z.1 (z.2 d))^2

theorem uncutTripleSquare_integrable {R : ℝ} (hR : 0 ≤ R) {θ : Thermodynamics.Parameter}
    (hθ : θ∈Thermodynamics.positiveDomain R) (f g h : C(MomentumDomain R,ScalarField))
    (a b d : Fin 4) : Integrable (uncutTripleSquare f g h a b d) (volume.prod (jointMeasure R θ)) := by
  letI:=jointMeasure_finite hR hθ
  have hmeas:=((leg_evaluate_measurable f a).mul (leg_evaluate_measurable g b)).mul
    (leg_evaluate_measurable h d)
  apply Integrable.of_bound (hmeas.pow_const 2).aestronglyMeasurable ((‖f‖*‖g‖*‖h‖)^2)
  apply ae_of_all
  intro z
  change ‖(evaluate f z.1 (z.2 a)*evaluate g z.1 (z.2 b)*evaluate h z.1 (z.2 d))^2‖ ≤ _
  rw [Real.norm_eq_abs,abs_pow,abs_mul,abs_mul]
  have hf:=evaluate_bound f z.1 (z.2 a)
  have hg:=evaluate_bound g z.1 (z.2 b)
  have hh:=evaluate_bound h z.1 (z.2 d)
  gcongr

theorem full_three_pointwise {R : ℝ} (p : JetSpace R) (a b d : Fin 4)
    (i j n : Fin 3) (η : ℝ) {κ M : ℝ}
    (hp : ∀k,amplitude p k ≤ M) (hbulk : ∀k,cut R η k=0 → amplitude p k ≤ κ)
    (q : FourMomenta) :
    (∫X,(evaluate (firstCubeSection p i) X (q a)*evaluate (firstCubeSection p j) X (q b)*
      evaluate (firstCubeSection p n) X (q d))^2) ≤
      threeSmallConstant κ M*massTriple p a b d q+2500*M^4*cutTripleMass p a b d η q := by
  let S:ℝ:=∫X,(evaluate (firstCubeSection p i) X (q a)*evaluate (firstCubeSection p j) X (q b)*
      evaluate (firstCubeSection p n) X (q d))^2
  change S ≤ _
  have he : cutTripleMass p a b d η q=massTriple p a b d q*cut R η (q a)*cut R η (q b)*cut R η (q d) :=
    cutTripleMass_identity p a b d η q
  have hm:=massTriple_nonnegative p a b d q
  have h0:=threeConstant_nonnegative κ M M
  have h1:=threeConstant_nonnegative M κ M
  have h2:=threeConstant_nonnegative M M κ
  have hz : 0 ≤ threeSmallConstant κ M:=add_nonneg (add_nonneg h0 h1) h2
  rcases cut_zero_or_one R η (q a) with ha|ha
  · have h : S ≤ threeConstant κ M M*massTriple p a b d q := by
      simpa only [S,massTriple,mul_assoc] using
        actual_three_amplitude_spatial p (q a) (q b) (q d) i j n (hbulk _ ha) (hp _) (hp _)
    rw [he,ha]
    simp only [mul_zero,zero_mul,add_zero]
    unfold threeSmallConstant
    nlinarith [mul_nonneg h1 hm,mul_nonneg h2 hm]
  · rcases cut_zero_or_one R η (q b) with hb|hb
    · have h : S ≤ threeConstant M κ M*massTriple p a b d q := by
        simpa only [S,massTriple,mul_assoc] using
          actual_three_amplitude_spatial p (q a) (q b) (q d) i j n (hp _) (hbulk _ hb) (hp _)
      rw [he,hb]
      simp only [mul_zero,zero_mul,add_zero]
      unfold threeSmallConstant
      nlinarith [mul_nonneg h0 hm,mul_nonneg h2 hm]
    · rcases cut_zero_or_one R η (q d) with hd|hd
      · have h : S ≤ threeConstant M M κ*massTriple p a b d q := by
          simpa only [S,massTriple,mul_assoc] using
            actual_three_amplitude_spatial p (q a) (q b) (q d) i j n (hp _) (hp _) (hbulk _ hd)
        rw [he,hd]
        simp only [mul_zero,add_zero]
        unfold threeSmallConstant
        nlinarith [mul_nonneg h0 hm,mul_nonneg h1 hm]
      · have h : S ≤ (2500*M^4)*massTriple p a b d q := by
          simpa only [S,massTriple,mul_assoc] using
            actual_three_spatial p (q a) (q b) (q d) i j n (hp _) (hp _) (hp _)
        rw [he,ha,hb,hd,mul_one,mul_one,mul_one]
        exact h.trans (le_add_of_nonneg_left (mul_nonneg hz hm))

/-- The entire three-leg derivative product, not only its corner part. -/
theorem actual_full_three_moser {R : ℝ} (hR : 0 ≤ R) {θ : Thermodynamics.Parameter}
    (hθ : θ∈Thermodynamics.positiveDomain R) (p : JetSpace R) (a b d : Fin 4)
    (hab : a≠b) (i j n : Fin 3) (η : ℝ) {κ M : ℝ}
    (hp : ∀k,amplitude p k ≤ M) (hbulk : ∀k,cut R η k=0 → amplitude p k ≤ κ) :
    (∫z,uncutTripleSquare (firstCubeSection p i) (firstCubeSection p j) (firstCubeSection p n) a b d z
      ∂volume.prod (jointMeasure R θ)) ≤
      (threeSmallConstant κ M+2500*M^4*(omega R θ η)^((2:ℝ)/3))*(∫k,mass p k∂marginal R θ) := by
  letI:=jointMeasure_finite hR hθ
  rw [integral_prod_symm _ (uncutTripleSquare_integrable hR hθ _ _ _ a b d)]
  have hmdata:=actual_massTriple_data hR hθ p a b d
  have hcdata:=actual_cutTripleMass_data hR hθ p a b d hab η
  have hi:=(hmdata.1.const_mul (threeSmallConstant κ M)).add (hcdata.1.const_mul (2500*M^4))
  have hm : (∫q,(∫X,(evaluate (firstCubeSection p i) X (q a)*evaluate (firstCubeSection p j) X (q b)*
      evaluate (firstCubeSection p n) X (q d))^2)∂jointMeasure R θ) ≤
      ∫q,threeSmallConstant κ M*massTriple p a b d q+2500*M^4*cutTripleMass p a b d η q
        ∂jointMeasure R θ := by
    apply integral_mono_of_nonneg (ae_of_all _ (fun q=>integral_nonneg (fun X=>sq_nonneg _))) hi
    exact ae_of_all _ (full_three_pointwise p a b d i j n η hp hbulk)
  rw [integral_add (hmdata.1.const_mul _) (hcdata.1.const_mul _),integral_const_mul,integral_const_mul] at hm
  have hz : 0 ≤ threeSmallConstant κ M:=add_nonneg
    (add_nonneg (threeConstant_nonnegative _ _ _) (threeConstant_nonnegative _ _ _))
    (threeConstant_nonnegative _ _ _)
  have h1:=mul_le_mul_of_nonneg_left hmdata.2 hz
  have h2:=mul_le_mul_of_nonneg_left hcdata.2 (show 0 ≤ 2500*M^4 by positivity)
  simp only [uncutTripleSquare]
  nlinarith

theorem threeSmallConstant_continuous (M : ℝ) : Continuous (fun κ:ℝ=>threeSmallConstant κ M) := by
  have h : Continuous (fun κ:ℝ=>(2500*κ^4)^((1:ℝ)/3)) :=
    (Real.continuous_rpow_const (by norm_num : (0:ℝ)≤1/3)).comp
      (continuous_const.mul (continuous_id.pow 4))
  unfold threeSmallConstant threeConstant
  exact (((h.mul continuous_const).mul continuous_const).add
    ((continuous_const.mul h).mul continuous_const)).add (continuous_const.mul h)

theorem threeSmallConstant_zero (M : ℝ) : threeSmallConstant 0 M=0 := by
  norm_num [threeSmallConstant,threeConstant]

theorem full_three_coefficient_tendsto {R : ℝ} (hR : 0<R) {θ : Thermodynamics.Parameter}
    (hθ : θ∈Thermodynamics.positiveDomain R) (M : ℝ) :
    Tendsto (fun z:ℝ×ℝ=>threeSmallConstant z.1 M+2500*M^4*(omega R θ z.2)^((2:ℝ)/3))
      (𝓝 ((0:ℝ),(0:ℝ))) (𝓝 0) := by
  have hb : Tendsto (fun z:ℝ×ℝ=>threeSmallConstant z.1 M) (𝓝 ((0:ℝ),(0:ℝ))) (𝓝 0) := by
    simpa only [Function.comp_def,threeSmallConstant_zero] using
      ((threeSmallConstant_continuous M).comp continuous_fst).tendsto ((0:ℝ),(0:ℝ))
  have hc : Tendsto (fun z:ℝ×ℝ=>(omega R θ z.2)^((2:ℝ)/3))
      (𝓝 ((0:ℝ),(0:ℝ))) (𝓝 0) := by
    have hw:=(omega_tendsto hR hθ).comp (continuous_snd.tendsto ((0:ℝ),(0:ℝ)))
    have hr:=((Real.continuous_rpow_const (by norm_num : (0:ℝ)≤2/3)).tendsto 0).comp hw
    norm_num at hr ⊢
    exact hr
  simpa only [mul_zero,add_zero] using hb.add (hc.const_mul (2500*M^4))

end
end Resonance.ActualThreeFullMoser
