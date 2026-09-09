import Resonance.SecondSpatialMassGN
import Resonance.ActualTwoOneFullMoser

/-! The full order-two 1+1 allocation on the same original quartet,
paid by its actual nine-component second spatial mass. -/
open Set MeasureTheory Filter
open scoped Topology ENNReal
namespace Resonance.ActualSecondFullMoser
noncomputable section
open ResonantMeasure WeightedJointMeasure FrequencyWeightedForm
open FreeTransport SpatialChainRule SpatialJetSpace SpatialIntegrationByParts
open SpatialMomentumSections SecondSpatialMassGN CornerPairTruncation JointCornerHolder
open ActualCornerSpatialMoser ActualTwoOneFullMoser
set_option maxHeartbeats 1800000

def massPair2 {R : ℝ} (p : JetSpace R) (a b : Fin 4) (q : FourMomenta) : ℝ:=
  Real.sqrt (mass2 p (q a))*Real.sqrt (mass2 p (q b))
def cutMassPair2 {R : ℝ} (p : JetSpace R) (a b : Fin 4) (η : ℝ) (q : FourMomenta) : ℝ:=
  (Real.sqrt (mass2 p (q a))*cut R η (q a))*(Real.sqrt (mass2 p (q b))*cut R η (q b))

theorem massPair2_nonnegative {R : ℝ} (p : JetSpace R) (a b : Fin 4) (q : FourMomenta) :
    0 ≤ massPair2 p a b q:=mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)

theorem massPair2_measurable {R : ℝ} (p : JetSpace R) (a b : Fin 4) :
    Measurable (massPair2 p a b) :=
  (Real.continuous_sqrt.measurable.comp ((mass2_measurable p).comp (measurable_pi_apply a))).mul
    (Real.continuous_sqrt.measurable.comp ((mass2_measurable p).comp (measurable_pi_apply b)))

theorem massPair2_arithmetic {R : ℝ} (p : JetSpace R) (a b : Fin 4) (q : FourMomenta) :
    massPair2 p a b q ≤ (1/2:ℝ)*mass2 p (q a)+(1/2:ℝ)*mass2 p (q b) := by
  have h:=sq_nonneg (Real.sqrt (mass2 p (q a))-Real.sqrt (mass2 p (q b)))
  have ha:=Real.sq_sqrt (mass2_nonnegative p (q a))
  have hb:=Real.sq_sqrt (mass2_nonnegative p (q b))
  unfold massPair2
  nlinarith

theorem actual_massPair2_data {R : ℝ} (hR : 0 ≤ R) {θ : Thermodynamics.Parameter}
    (hθ : θ∈Thermodynamics.positiveDomain R) (p : JetSpace R) (a b : Fin 4) :
    Integrable (massPair2 p a b) (jointMeasure R θ) ∧
    (∫q,massPair2 p a b q∂jointMeasure R θ) ≤ ∫k,mass2 p k∂marginal R θ := by
  letI:=actual_marginal_finite hR hθ
  have hi (i:Fin 4) := (all_legs_preserve R θ i).integrable_comp_of_integrable
    (mass2_integrable p (marginal R θ))
  have hr:=((hi a).const_mul (1/2:ℝ)).add ((hi b).const_mul (1/2:ℝ))
  have hs : Integrable (massPair2 p a b) (jointMeasure R θ) := by
    apply hr.mono' (massPair2_measurable p a b).aestronglyMeasurable
    apply ae_of_all
    intro q
    rw [Real.norm_eq_abs,abs_of_nonneg (massPair2_nonnegative p a b q)]
    exact massPair2_arithmetic p a b q
  constructor
  · exact hs
  · have hb:=integral_mono hs hr (massPair2_arithmetic p a b)
    have hsum:=integral_add ((hi a).const_mul (1/2:ℝ)) ((hi b).const_mul (1/2:ℝ))
    simp only [Pi.add_apply,Function.comp_def] at hb hsum
    simp only [integral_const_mul] at hsum
    rw [hsum,actual_leg_integral R θ a (mass2_integrable p _),
      actual_leg_integral R θ b (mass2_integrable p _)] at hb
    linarith

theorem cutMassPair2_identity {R : ℝ} (p : JetSpace R) (a b : Fin 4) (η : ℝ) (q : FourMomenta) :
    cutMassPair2 p a b η q=massPair2 p a b q*cut R η (q a)*cut R η (q b) := by
  unfold cutMassPair2 massPair2
  ring

theorem actual_cutMassPair2_data {R : ℝ} (hR : 0 ≤ R) {θ : Thermodynamics.Parameter}
    (hθ : θ∈Thermodynamics.positiveDomain R) (p : JetSpace R) (a b : Fin 4)
    (hab : a≠b) (η : ℝ) :
    Integrable (cutMassPair2 p a b η) (jointMeasure R θ) ∧
    (∫q,cutMassPair2 p a b η q∂jointMeasure R θ) ≤
      omega R θ η*(∫k,mass2 p k∂marginal R θ) := by
  have hi : Integrable (cutMassPair2 p a b η) (jointMeasure R θ) := by
    unfold cutMassPair2
    exact actual_cut_pair_integrable (R:=R) (θ:=θ) a b η
      (f:=fun k=>Real.sqrt (mass2 p k)) (g:=fun k=>Real.sqrt (mass2 p k))
      (actual_mass2_sqrt_memLp hR hθ p) (actual_mass2_sqrt_memLp hR hθ p)
  refine ⟨hi,?_⟩
  have hb:=actual_nonnegative_pair_bound a b hab η (actual_mass2_sqrt_memLp hR hθ p)
    (actual_mass2_sqrt_memLp hR hθ p) (fun _=>Real.sqrt_nonneg _) (fun _=>Real.sqrt_nonneg _)
  simp only [Real.sq_sqrt (mass2_nonnegative p _)] at hb
  rw [mul_assoc,Real.mul_self_sqrt (integral_nonneg (mass2_nonnegative p))] at hb
  exact hb

theorem full_second_pointwise {R : ℝ} (p : JetSpace R) (a b : Fin 4)
    (i j : Fin 3) (η : ℝ) {κ M : ℝ} (hκ : 0 ≤ κ) (hM : 0 ≤ M)
    (hp : ∀k,amplitude p k ≤ M) (hbulk : ∀k,cut R η k=0 → amplitude p k ≤ κ)
    (q : FourMomenta) :
    (∫X,(evaluate (firstCubeSection p i) X (q a)*evaluate (firstCubeSection p j) X (q b))^2) ≤
      18*κ*M*massPair2 p a b q+9*M^2*cutMassPair2 p a b η q := by
  let S:ℝ:=∫X,(evaluate (firstCubeSection p i) X (q a)*evaluate (firstCubeSection p j) X (q b))^2
  change S ≤ _
  have he:=cutMassPair2_identity p a b η q
  have hm:=massPair2_nonnegative p a b q
  rcases cut_zero_or_one R η (q a) with ha|ha
  · have h : S ≤9*κ*M*massPair2 p a b q := by
      simpa only [S,massPair2,mul_assoc] using actual_two_first_spatial p (q a) (q b) i j (hbulk _ ha) (hp _)
    rw [he,ha]
    simp only [mul_zero,zero_mul,add_zero]
    nlinarith [mul_nonneg (mul_nonneg hκ hM) hm]
  · rcases cut_zero_or_one R η (q b) with hb|hb
    · have h : S ≤9*M*κ*massPair2 p a b q := by
        simpa only [S,massPair2,mul_assoc] using actual_two_first_spatial p (q a) (q b) i j (hp _) (hbulk _ hb)
      rw [he,hb]
      simp only [mul_zero,add_zero]
      nlinarith [mul_nonneg (mul_nonneg hκ hM) hm]
    · have h : S ≤9*M*M*massPair2 p a b q := by
        simpa only [S,massPair2,mul_assoc] using actual_two_first_spatial p (q a) (q b) i j (hp _) (hp _)
      rw [he,ha,hb,mul_one,mul_one]
      nlinarith [mul_nonneg (mul_nonneg hκ hM) hm]

/-- The whole order-two product is paid by the actual H² mass. -/
theorem actual_full_second_moser {R : ℝ} (hR : 0 ≤ R) {θ : Thermodynamics.Parameter}
    (hθ : θ∈Thermodynamics.positiveDomain R) (p : JetSpace R) (a b : Fin 4)
    (hab : a≠b) (i j : Fin 3) (η : ℝ) {κ M : ℝ} (hκ : 0 ≤ κ) (hM : 0 ≤ M)
    (hp : ∀k,amplitude p k ≤ M) (hbulk : ∀k,cut R η k=0 → amplitude p k ≤ κ) :
    (∫z,uncutPairSquare (firstCubeSection p i) (firstCubeSection p j) a b z
      ∂volume.prod (jointMeasure R θ)) ≤
      (18*κ*M+9*M^2*omega R θ η)*(∫k,mass2 p k∂marginal R θ) := by
  letI:=jointMeasure_finite hR hθ
  rw [integral_prod_symm _ (uncutPairSquare_integrable hR hθ _ _ a b)]
  have hd:=actual_massPair2_data hR hθ p a b
  have hc:=actual_cutMassPair2_data hR hθ p a b hab η
  have hi:=(hd.1.const_mul (18*κ*M)).add (hc.1.const_mul (9*M^2))
  have hm : (∫q,(∫X,(evaluate (firstCubeSection p i) X (q a)*
      evaluate (firstCubeSection p j) X (q b))^2)∂jointMeasure R θ) ≤
      ∫q,18*κ*M*massPair2 p a b q+9*M^2*cutMassPair2 p a b η q∂jointMeasure R θ := by
    apply integral_mono_of_nonneg (ae_of_all _ (fun q=>integral_nonneg (fun X=>sq_nonneg _))) hi
    exact ae_of_all _ (full_second_pointwise p a b i j η hκ hM hp hbulk)
  rw [integral_add (hd.1.const_mul _) (hc.1.const_mul _),integral_const_mul,integral_const_mul] at hm
  have h1:=mul_le_mul_of_nonneg_left hd.2 (show 0 ≤ 18*κ*M by positivity)
  have h2:=mul_le_mul_of_nonneg_left hc.2 (show 0 ≤ 9*M^2 by positivity)
  simp only [uncutPairSquare]
  nlinarith

theorem full_second_coefficient_tendsto {R : ℝ} (hR : 0<R) {θ : Thermodynamics.Parameter}
    (hθ : θ∈Thermodynamics.positiveDomain R) (M : ℝ) :
    Tendsto (fun z:ℝ×ℝ=>18*z.1*M+9*M^2*omega R θ z.2)
      (𝓝 ((0:ℝ),(0:ℝ))) (𝓝 0) := by
  have hb : Tendsto (fun z:ℝ×ℝ=>18*z.1*M) (𝓝 ((0:ℝ),(0:ℝ))) (𝓝 0) := by
    simpa only [Pi.mul_apply,mul_zero,zero_mul] using
      (((continuous_const.mul continuous_fst).mul continuous_const).tendsto ((0:ℝ),(0:ℝ)) :
        Tendsto (fun z:ℝ×ℝ=>18*z.1*M) _ _)
  have hc:=(omega_tendsto hR hθ).comp (continuous_snd.tendsto ((0:ℝ),(0:ℝ)))
  simpa only [mul_zero,add_zero] using hb.add (hc.const_mul (9*M^2))

end
end Resonance.ActualSecondFullMoser
