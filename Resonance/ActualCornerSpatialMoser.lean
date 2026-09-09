import Resonance.SpatialProductGN

/-! Actual mixed 2+1 spatial products on one full weighted quartet.
Both the derivative fields and their corner cutoffs are kept at their
actual legs; the common spatial point is integrated before the original
joint momentum law. -/
open Set MeasureTheory Filter
open scoped Topology ENNReal
namespace Resonance.ActualCornerSpatialMoser
noncomputable section
open ResonantMeasure WeightedJointMeasure FrequencyWeightedForm
open FreeTransport SpatialChainRule SpatialJetSpace SpatialIntegrationByParts
open SpatialMomentumSections SpatialProductGN CornerPairTruncation JointCornerHolder
set_option maxHeartbeats 1800000

def pairSquare {R : ℝ} (f g : C(MomentumDomain R,ScalarField))
    (a b : Fin 4) (η : ℝ) (z : SpatialTorus×FourMomenta) : ℝ:=
  (evaluate f z.1 (z.2 a)*evaluate g z.1 (z.2 b))^2*
    cut R η (z.2 a)*cut R η (z.2 b)

theorem pairSquare_measurable {R : ℝ} (f g : C(MomentumDomain R,ScalarField))
    (a b : Fin 4) (η : ℝ) : Measurable (pairSquare f g a b η) := by
  have hc (i:Fin 4) : Measurable (fun z:SpatialTorus×FourMomenta=>cut R η (z.2 i)):=
    (cut_measurable R η).comp ((measurable_pi_apply i).comp measurable_snd)
  exact ((((leg_evaluate_measurable f a).mul (leg_evaluate_measurable g b)).pow_const 2).mul
    (hc a)).mul (hc b)

theorem pairSquare_nonnegative {R : ℝ} (f g : C(MomentumDomain R,ScalarField))
    (a b : Fin 4) (η : ℝ) (z : SpatialTorus×FourMomenta) : 0 ≤ pairSquare f g a b η z :=
  mul_nonneg (mul_nonneg (sq_nonneg _) (cut_bounds R η _).1) (cut_bounds R η _).1

theorem pairSquare_bound {R : ℝ} (f g : C(MomentumDomain R,ScalarField))
    (a b : Fin 4) (η : ℝ) (z : SpatialTorus×FourMomenta) :
    ‖pairSquare f g a b η z‖ ≤ (‖f‖*‖g‖)^2 := by
  unfold pairSquare
  rw [Real.norm_eq_abs,abs_mul,abs_mul,abs_pow,abs_mul]
  have hf:=evaluate_bound f z.1 (z.2 a)
  have hg:=evaluate_bound g z.1 (z.2 b)
  have hc:=(cut_bounds R η (z.2 a)).2
  have hd:=(cut_bounds R η (z.2 b)).2
  calc
    _ ≤ (‖f‖*‖g‖)^2*1*1 := by gcongr
    _ =_ := by ring

theorem pairSquare_integrable {R : ℝ} (hR : 0 ≤ R) {θ : Thermodynamics.Parameter}
    (hθ : θ∈Thermodynamics.positiveDomain R) (f g : C(MomentumDomain R,ScalarField))
    (a b : Fin 4) (η : ℝ) :
    Integrable (pairSquare f g a b η) (volume.prod (jointMeasure R θ)) := by
  letI:=jointMeasure_finite hR hθ
  exact Integrable.of_bound (pairSquare_measurable f g a b η).aestronglyMeasurable
    ((‖f‖*‖g‖)^2) (ae_of_all _ (pairSquare_bound f g a b η))

theorem pairSquare_fubini {R : ℝ} (hR : 0 ≤ R) {θ : Thermodynamics.Parameter}
    (hθ : θ∈Thermodynamics.positiveDomain R) (f g : C(MomentumDomain R,ScalarField))
    (a b : Fin 4) (η : ℝ) :
    (∫z,pairSquare f g a b η z∂volume.prod (jointMeasure R θ))=
      ∫q,(∫X,(evaluate f X (q a)*evaluate g X (q b))^2)*cut R η (q a)*cut R η (q b)
        ∂jointMeasure R θ := by
  letI:=jointMeasure_finite hR hθ
  rw [integral_prod_symm _ (pairSquare_integrable hR hθ f g a b η)]
  simp only [pairSquare,integral_mul_const]

def cutMassProduct {R : ℝ} (p : JetSpace R) (a b : Fin 4) (η : ℝ) (q : FourMomenta) : ℝ:=
  (Real.sqrt (mass p (q a))*cut R η (q a))^((4:ℝ)/3)*
    (Real.sqrt (mass p (q b))*cut R η (q b))^((2:ℝ)/3)

theorem cut_zero_or_one (R η : ℝ) (k : E) : cut R η k=0 ∨ cut R η k=1 := by
  by_cases hk:k∈CornerNewtonTail.fullTail R η <;> simp [cut,hk]

theorem cutMassProduct_identity {R : ℝ} (p : JetSpace R) (a b : Fin 4)
    (η : ℝ) (q : FourMomenta) :
    cutMassProduct p a b η q=(mass p (q a))^((2:ℝ)/3)*(mass p (q b))^((1:ℝ)/3)*
      cut R η (q a)*cut R η (q b) := by
  unfold cutMassProduct
  rcases cut_zero_or_one R η (q a) with h0|h1
  · norm_num [h0]
  · rcases cut_zero_or_one R η (q b) with h0|h2
    · norm_num [h0]
    · simp only [h1,h2,mul_one]
      rw [Real.sqrt_eq_rpow,Real.sqrt_eq_rpow,←Real.rpow_mul (mass_nonnegative p (q a)),
        ←Real.rpow_mul (mass_nonnegative p (q b))]
      norm_num

theorem cutMassProduct_integrable {R : ℝ} (hR : 0 ≤ R) {θ : Thermodynamics.Parameter}
    (hθ : θ∈Thermodynamics.positiveDomain R) (p : JetSpace R) (a b : Fin 4) (η : ℝ) :
    Integrable (cutMassProduct p a b η) (jointMeasure R θ) := by
  unfold cutMassProduct
  exact actual_two_one_corner_integrable (R:=R) (θ:=θ) a b η
    (f:=fun k=>Real.sqrt (mass p k)) (g:=fun k=>Real.sqrt (mass p k))
    (actual_mass_sqrt_memLp hR hθ p) (actual_mass_sqrt_memLp hR hθ p)
    (fun k=>Real.sqrt_nonneg (mass p k)) (fun k=>Real.sqrt_nonneg (mass p k))

theorem actual_cutMassProduct_bound {R : ℝ} (hR : 0 ≤ R) {θ : Thermodynamics.Parameter}
    (hθ : θ∈Thermodynamics.positiveDomain R) (p : JetSpace R) (a b : Fin 4)
    (hab : a≠b) (η : ℝ) :
    (∫q,cutMassProduct p a b η q∂jointMeasure R θ) ≤
      (omega R θ η)^((2:ℝ)/3)*(∫k,mass p k∂marginal R θ) := by
  have h:=actual_two_one_corner_bound a b hab η (actual_mass_sqrt_memLp hR hθ p)
    (actual_mass_sqrt_memLp hR hθ p) (fun _=>Real.sqrt_nonneg _) (fun _=>Real.sqrt_nonneg _)
  simp only [Real.sq_sqrt (mass_nonnegative p _)] at h
  have he : (∫k,mass p k∂marginal R θ)^((2:ℝ)/3)*(∫k,mass p k∂marginal R θ)^((1:ℝ)/3)=
      ∫k,mass p k∂marginal R θ := by
    rw [←Real.rpow_add_of_nonneg (integral_nonneg (mass_nonnegative p)) (by norm_num) (by norm_num)]
    norm_num
  simpa only [mul_assoc,he] using h

/-- The actual squared L² bound for a corner-localized 2+1 derivative
allocation, with all spatial points and momentum legs still joint. -/
theorem actual_two_one_corner_moser {R : ℝ} (hR : 0 ≤ R) {θ : Thermodynamics.Parameter}
    (hθ : θ∈Thermodynamics.positiveDomain R) (p : JetSpace R) (a b : Fin 4)
    (hab : a≠b) (i j n : Fin 3) (η : ℝ) {M : ℝ} (hM : 0 ≤ M)
    (hp : ∀k,amplitude p k ≤ M) :
    (∫z,pairSquare (secondCubeSection p i j) (firstCubeSection p n) a b η z
      ∂volume.prod (jointMeasure R θ)) ≤
      twoOneConstant M*(omega R θ η)^((2:ℝ)/3)*(∫k,mass p k∂marginal R θ) := by
  rw [pairSquare_fubini hR hθ]
  have hi:=((cutMassProduct_integrable hR hθ p a b η).const_mul (twoOneConstant M))
  have hm : (∫q,(∫X,(evaluate (secondCubeSection p i j) X (q a)*
      evaluate (firstCubeSection p n) X (q b))^2)*cut R η (q a)*cut R η (q b)∂jointMeasure R θ) ≤
      ∫q,twoOneConstant M*cutMassProduct p a b η q∂jointMeasure R θ := by
    apply integral_mono_of_nonneg
      (ae_of_all _ (fun q=>mul_nonneg (mul_nonneg (integral_nonneg (fun X=>sq_nonneg _))
        (cut_bounds R η _).1) (cut_bounds R η _).1)) hi
    apply ae_of_all
    intro q
    have h:=actual_two_one_spatial p (q a) (q b) i j n hM (hp _) (hp _)
    have hb:=mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right h (cut_bounds R η (q a)).1) (cut_bounds R η (q b)).1
    dsimp only
    rw [cutMassProduct_identity]
    simpa only [mul_assoc] using hb
  rw [integral_const_mul] at hm
  exact hm.trans (by
    have h:=mul_le_mul_of_nonneg_left (actual_cutMassProduct_bound hR hθ p a b hab η)
      (twoOneConstant_nonneg hM)
    simpa only [mul_assoc] using h)

def tripleSquare {R : ℝ} (f g h : C(MomentumDomain R,ScalarField))
    (a b d : Fin 4) (η : ℝ) (z : SpatialTorus×FourMomenta) : ℝ:=
  (evaluate f z.1 (z.2 a)*evaluate g z.1 (z.2 b)*evaluate h z.1 (z.2 d))^2*
    cut R η (z.2 a)*cut R η (z.2 b)*cut R η (z.2 d)

theorem tripleSquare_measurable {R : ℝ} (f g h : C(MomentumDomain R,ScalarField))
    (a b d : Fin 4) (η : ℝ) : Measurable (tripleSquare f g h a b d η) := by
  have hc (i:Fin 4) : Measurable (fun z:SpatialTorus×FourMomenta=>cut R η (z.2 i)):=
    (cut_measurable R η).comp ((measurable_pi_apply i).comp measurable_snd)
  exact ((((((leg_evaluate_measurable f a).mul (leg_evaluate_measurable g b)).mul
    (leg_evaluate_measurable h d)).pow_const 2).mul (hc a)).mul (hc b)).mul (hc d)

theorem tripleSquare_bound {R : ℝ} (f g h : C(MomentumDomain R,ScalarField))
    (a b d : Fin 4) (η : ℝ) (z : SpatialTorus×FourMomenta) :
    ‖tripleSquare f g h a b d η z‖ ≤ (‖f‖*‖g‖*‖h‖)^2 := by
  unfold tripleSquare
  rw [Real.norm_eq_abs,abs_mul,abs_mul,abs_mul,abs_pow,abs_mul,abs_mul]
  have hf:=evaluate_bound f z.1 (z.2 a)
  have hg:=evaluate_bound g z.1 (z.2 b)
  have hh:=evaluate_bound h z.1 (z.2 d)
  have hc:=(cut_bounds R η (z.2 a)).2
  have hd:=(cut_bounds R η (z.2 b)).2
  have he:=(cut_bounds R η (z.2 d)).2
  calc
    _ ≤ (‖f‖*‖g‖*‖h‖)^2*1*1*1 := by gcongr
    _ =_ := by ring

theorem tripleSquare_integrable {R : ℝ} (hR : 0 ≤ R) {θ : Thermodynamics.Parameter}
    (hθ : θ∈Thermodynamics.positiveDomain R) (f g h : C(MomentumDomain R,ScalarField))
    (a b d : Fin 4) (η : ℝ) :
    Integrable (tripleSquare f g h a b d η) (volume.prod (jointMeasure R θ)) := by
  letI:=jointMeasure_finite hR hθ
  exact Integrable.of_bound (tripleSquare_measurable f g h a b d η).aestronglyMeasurable
    ((‖f‖*‖g‖*‖h‖)^2) (ae_of_all _ (tripleSquare_bound f g h a b d η))

theorem tripleSquare_fubini {R : ℝ} (hR : 0 ≤ R) {θ : Thermodynamics.Parameter}
    (hθ : θ∈Thermodynamics.positiveDomain R) (f g h : C(MomentumDomain R,ScalarField))
    (a b d : Fin 4) (η : ℝ) :
    (∫z,tripleSquare f g h a b d η z∂volume.prod (jointMeasure R θ))=
      ∫q,(∫X,(evaluate f X (q a)*evaluate g X (q b)*evaluate h X (q d))^2)*
        cut R η (q a)*cut R η (q b)*cut R η (q d)∂jointMeasure R θ := by
  letI:=jointMeasure_finite hR hθ
  rw [integral_prod_symm _ (tripleSquare_integrable hR hθ f g h a b d η)]
  simp only [tripleSquare,integral_mul_const]

def cutTripleMass {R : ℝ} (p : JetSpace R) (a b d : Fin 4) (η : ℝ) (q : FourMomenta) : ℝ:=
  (Real.sqrt (mass p (q a))*cut R η (q a))^((2:ℝ)/3)*
    (Real.sqrt (mass p (q b))*cut R η (q b))^((2:ℝ)/3)*
      (Real.sqrt (mass p (q d))*cut R η (q d))^((2:ℝ)/3)

theorem sqrt_cut_two_thirds {R : ℝ} (p : JetSpace R) (η : ℝ) (k : E) :
    (Real.sqrt (mass p k)*cut R η k)^((2:ℝ)/3)=
      (mass p k)^((1:ℝ)/3)*cut R η k := by
  rcases cut_zero_or_one R η k with h0|h1
  · norm_num [h0]
  · simp only [h1,mul_one]
    rw [Real.sqrt_eq_rpow,←Real.rpow_mul (mass_nonnegative p k)]
    norm_num

theorem cutTripleMass_identity {R : ℝ} (p : JetSpace R) (a b d : Fin 4)
    (η : ℝ) (q : FourMomenta) : cutTripleMass p a b d η q=
      (mass p (q a))^((1:ℝ)/3)*(mass p (q b))^((1:ℝ)/3)*(mass p (q d))^((1:ℝ)/3)*
      cut R η (q a)*cut R η (q b)*cut R η (q d) := by
  unfold cutTripleMass
  rw [sqrt_cut_two_thirds,sqrt_cut_two_thirds,sqrt_cut_two_thirds]
  ring

theorem actual_cutTripleMass_data {R : ℝ} (hR : 0 ≤ R) {θ : Thermodynamics.Parameter}
    (hθ : θ∈Thermodynamics.positiveDomain R) (p : JetSpace R) (a b d : Fin 4)
    (hab : a≠b) (η : ℝ) :
    Integrable (cutTripleMass p a b d η) (jointMeasure R θ) ∧
    (∫q,cutTripleMass p a b d η q∂jointMeasure R θ) ≤
      (omega R θ η)^((2:ℝ)/3)*(∫k,mass p k∂marginal R θ) := by
  have h:=actual_three_leg_corner_data a b d hab η (actual_mass_sqrt_memLp hR hθ p)
    (actual_mass_sqrt_memLp hR hθ p) (actual_mass_sqrt_memLp hR hθ p)
    (fun _=>Real.sqrt_nonneg _) (fun _=>Real.sqrt_nonneg _) (fun _=>Real.sqrt_nonneg _)
  constructor
  · exact h.1
  · have hb:=h.2
    simp only [Real.sq_sqrt (mass_nonnegative p _)] at hb
    have he : ((∫k,mass p k∂marginal R θ)^((1:ℝ)/3))^3=
        ∫k,mass p k∂marginal R θ := by
      rw [←Real.rpow_natCast,←Real.rpow_mul (integral_nonneg (mass_nonnegative p))]
      norm_num
    have hr : (omega R θ η)^((2:ℝ)/3)*(∫k,mass p k∂marginal R θ)^((1:ℝ)/3)*
        (∫k,mass p k∂marginal R θ)^((1:ℝ)/3)*(∫k,mass p k∂marginal R θ)^((1:ℝ)/3)=
        (omega R θ η)^((2:ℝ)/3)*(∫k,mass p k∂marginal R θ) := by
      calc
        _ =(omega R θ η)^((2:ℝ)/3)*((∫k,mass p k∂marginal R θ)^((1:ℝ)/3))^3 := by ring
        _ =_ := by rw [he]
    exact hb.trans_eq hr

/-- The full 1+1+1 allocation. Distinctness is needed for one actual
pair only; no replacement by independent momentum marginals is made. -/
theorem actual_three_corner_moser {R : ℝ} (hR : 0 ≤ R) {θ : Thermodynamics.Parameter}
    (hθ : θ∈Thermodynamics.positiveDomain R) (p : JetSpace R) (a b d : Fin 4)
    (hab : a≠b) (i j n : Fin 3) (η : ℝ) {M : ℝ}
    (hp : ∀k,amplitude p k ≤ M) :
    (∫z,tripleSquare (firstCubeSection p i) (firstCubeSection p j) (firstCubeSection p n) a b d η z
      ∂volume.prod (jointMeasure R θ)) ≤
      2500*M^4*(omega R θ η)^((2:ℝ)/3)*(∫k,mass p k∂marginal R θ) := by
  rw [tripleSquare_fubini hR hθ]
  have hdata:=actual_cutTripleMass_data hR hθ p a b d hab η
  have hm : (∫q,(∫X,(evaluate (firstCubeSection p i) X (q a)*
      evaluate (firstCubeSection p j) X (q b)*evaluate (firstCubeSection p n) X (q d))^2)*
        cut R η (q a)*cut R η (q b)*cut R η (q d)∂jointMeasure R θ) ≤
      ∫q,(2500*M^4)*cutTripleMass p a b d η q∂jointMeasure R θ := by
    apply integral_mono_of_nonneg
      (ae_of_all _ (fun q=>mul_nonneg (mul_nonneg (mul_nonneg
        (integral_nonneg (fun X=>sq_nonneg _)) (cut_bounds R η _).1)
          (cut_bounds R η _).1) (cut_bounds R η _).1)) (hdata.1.const_mul _)
    apply ae_of_all
    intro q
    have h:=actual_three_spatial p (q a) (q b) (q d) i j n (hp _) (hp _) (hp _)
    have hb:=mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right h (cut_bounds R η (q a)).1) (cut_bounds R η (q b)).1)
        (cut_bounds R η (q d)).1
    dsimp only
    rw [cutTripleMass_identity]
    simpa only [mul_assoc] using hb
  rw [integral_const_mul] at hm
  exact hm.trans (by
    have h:=mul_le_mul_of_nonneg_left hdata.2 (show 0 ≤ 2500*M^4 by positivity)
    simpa only [mul_assoc] using h)

end
end Resonance.ActualCornerSpatialMoser
