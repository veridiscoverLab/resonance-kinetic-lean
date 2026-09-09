import Resonance.ActualSecondFullMoser
import Resonance.ActualThreeFullMoser

/-! Energy tests remain the full incoming-minus-outgoing difference of one
continuous spatial/momentum section. All estimates use the same actual
spatial/quartet product measure; integrability precedes every pairing. -/
open Set MeasureTheory
open scoped ENNReal
namespace Resonance.JointEnergyReader
noncomputable section
open ResonantMeasure WeightedJointMeasure FrequencyWeightedForm
open FreeTransport SpatialIntegrationByParts SpatialMomentumSections JointCornerHolder
set_option maxHeartbeats 1800000
local instance : MeasurableSpace ScalarField:=borel ScalarField
local instance : BorelSpace ScalarField:=⟨rfl⟩

abbrev Section (R : ℝ) := C(MomentumDomain R,ScalarField)
abbrev History := SpatialTorus×FourMomenta

def leg {R : ℝ} (h : Section R) (i : Fin 4) (z : History) : ℝ :=
  evaluate h z.1 (z.2 i)

def fullDifference {R : ℝ} (h : Section R) (z : History) : ℝ :=
  Collision.delta (fun i=>leg h i z)

def sectionMass {R : ℝ} (h : Section R) (k : E) : ℝ :=
  integralCLM ((zeroSection h k)^2)

theorem sectionMass_measurable {R : ℝ} (h : Section R) : Measurable (sectionMass h) := by
  exact integralCLM.continuous.measurable.comp ((zeroSection_measurable h).pow_const 2)

theorem sectionMass_nonnegative {R : ℝ} (h : Section R) (k : E) : 0 ≤ sectionMass h k :=
  integral_nonneg (fun _=>sq_nonneg _)

theorem sectionMass_integrable {R : ℝ} (h : Section R) (μ : Measure E) [IsFiniteMeasure μ] :
    Integrable (sectionMass h) μ := by
  have hf:=(evaluate_square_integrable h μ).integral_prod_right
  exact hf

theorem leg_memLp {R : ℝ} (hR : 0 ≤ R) {θ : Thermodynamics.Parameter}
    (hθ : θ∈Thermodynamics.positiveDomain R) (h : Section R) (i : Fin 4) :
    MemLp (leg h i) 2 (volume.prod (jointMeasure R θ)) :=
  (memLp_two_iff_integrable_sq (leg_evaluate_measurable h i).aestronglyMeasurable).mpr
    (leg_evaluate_square_integrable hR hθ h i)

theorem fullDifference_memLp {R : ℝ} (hR : 0 ≤ R) {θ : Thermodynamics.Parameter}
    (hθ : θ∈Thermodynamics.positiveDomain R) (h : Section R) :
    MemLp (fullDifference h) 2 (volume.prod (jointMeasure R θ)) :=
  (((leg_memLp hR hθ h 0).add (leg_memLp hR hθ h 1)).sub
    (leg_memLp hR hθ h 2)).sub (leg_memLp hR hθ h 3)

theorem actual_leg_square_integral {R : ℝ} (hR : 0 ≤ R) {θ : Thermodynamics.Parameter}
    (hθ : θ∈Thermodynamics.positiveDomain R) (h : Section R) (i : Fin 4) :
    (∫z,(leg h i z)^2∂volume.prod (jointMeasure R θ))=
      ∫k,sectionMass h k∂marginal R θ := by
  letI:=jointMeasure_finite hR hθ
  letI:=actual_marginal_finite hR hθ
  unfold leg
  rw [integral_prod_symm _ (leg_evaluate_square_integrable hR hθ h i)]
  exact actual_leg_integral R θ i (sectionMass_integrable h _)

theorem delta_square_bound (v : Fin 4→ℝ) :
    (Collision.delta v)^2 ≤ 4*((v 0)^2+(v 1)^2+(v 2)^2+(v 3)^2) := by
  unfold Collision.delta
  nlinarith [sq_nonneg (v 0-v 1),sq_nonneg (v 2-v 3),
    sq_nonneg (v 0+v 1+v 2+v 3)]

theorem actual_fullDifference_square {R : ℝ} (hR : 0 ≤ R) {θ : Thermodynamics.Parameter}
    (hθ : θ∈Thermodynamics.positiveDomain R) (h : Section R) :
    (∫z,(fullDifference h z)^2∂volume.prod (jointMeasure R θ)) ≤
      16*(∫k,sectionMass h k∂marginal R θ) := by
  have hi (i:Fin 4):=leg_evaluate_square_integrable hR hθ h i
  have hs:=((hi 0).add (hi 1)).add (hi 2)
  have ht:=hs.add (hi 3)
  have hd:=(memLp_two_iff_integrable_sq (fullDifference_memLp hR hθ h).aestronglyMeasurable).mp
    (fullDifference_memLp hR hθ h)
  have hb:=integral_mono hd (ht.const_mul 4) (fun z=>delta_square_bound (fun i=>leg h i z))
  have h1:=integral_add (hi 0) (hi 1)
  have h2:=integral_add ((hi 0).add (hi 1)) (hi 2)
  have h3:=integral_add hs (hi 3)
  simp only [Pi.add_apply] at hb h1 h2 h3
  rw [h1] at h2
  rw [h2] at h3
  rw [integral_const_mul,h3] at hb
  simp only [show ∀i:Fin 4,(∫z,(evaluate h z.1 (z.2 i))^2∂volume.prod (jointMeasure R θ))=
      ∫k,sectionMass h k∂marginal R θ from actual_leg_square_integral hR hθ h] at hb
  linarith

theorem square_pairing_data {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f g : α→ℝ} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    Integrable (fun z=>f z*g z) μ ∧
    |∫z,f z*g z∂μ| ≤ Real.sqrt (∫z,(f z)^2∂μ)*Real.sqrt (∫z,(g z)^2∂μ) := by
  refine ⟨hf.integrable_mul hg,?_⟩
  have hb:=abs_real_inner_le_norm (hf.toLp f) (hg.toLp g)
  have he : inner ℝ (hf.toLp f) (hg.toLp g)=∫z,f z*g z∂μ := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hf.coeFn_toLp,hg.coeFn_toLp] with z hfz hgz
    change (hg.toLp g z)*(hf.toLp f z)=_
    rw [hfz,hgz,mul_comm]
  rw [he,FixedMultiplier.L2_norm_eq_sqrt,FixedMultiplier.L2_norm_eq_sqrt] at hb
  simpa only [Real.norm_eq_abs,sq_abs] using hb

/-- Every single test parent and their full signed sum is absolutely
integrable against the actual L² mixed-derivative current. -/
theorem actual_full_test_pairing {R : ℝ} (hR : 0 ≤ R) {θ : Thermodynamics.Parameter}
    (hθ : θ∈Thermodynamics.positiveDomain R) (h : Section R) {P : History→ℝ}
    (hP : MemLp P 2 (volume.prod (jointMeasure R θ))) :
    (∀i:Fin 4,Integrable (fun z=>P z*leg h i z) (volume.prod (jointMeasure R θ))) ∧
    Integrable (fun z=>P z*fullDifference h z) (volume.prod (jointMeasure R θ)) ∧
    |∫z,P z*fullDifference h z∂volume.prod (jointMeasure R θ)| ≤
      4*Real.sqrt (∫z,(P z)^2∂volume.prod (jointMeasure R θ))*
        Real.sqrt (∫k,sectionMass h k∂marginal R θ) := by
  have hd:=square_pairing_data hP (fullDifference_memLp hR hθ h)
  refine ⟨fun i=>hP.integrable_mul (leg_memLp hR hθ h i),hd.1,?_⟩
  have hb:=Real.sqrt_le_sqrt (actual_fullDifference_square hR hθ h)
  rw [Real.sqrt_mul (by norm_num : (0:ℝ)≤16)] at hb
  norm_num at hb
  have hh:=mul_le_mul_of_nonneg_left hb
    (Real.sqrt_nonneg (∫z,(P z)^2∂volume.prod (jointMeasure R θ)))
  exact hd.2.trans (by nlinarith [hh])

theorem bounded_weight_memLp {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {P W : α→ℝ} (hP : MemLp P 2 μ) (hW : Measurable W) {B : ℝ}
    (hB : ∀z,|W z| ≤ B) :
    MemLp (fun z=>W z*P z) 2 μ ∧
    (∫z,(W z*P z)^2∂μ) ≤ B^2*(∫z,(P z)^2∂μ) := by
  have hi:=(memLp_two_iff_integrable_sq hP.aestronglyMeasurable).mp hP
  have hb (z:α) : (W z*P z)^2 ≤ B^2*(P z)^2 := by
    rw [mul_pow]
    apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
    simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg (W z)) (hB z) 2
  have hm:=(hW.aestronglyMeasurable.mul hP.aestronglyMeasurable).pow 2
  have hw : Integrable (fun z=>(W z*P z)^2) μ := by
    apply (hi.const_mul (B^2)).mono' hm
    apply ae_of_all
    intro z
    change |(W z*P z)^2| ≤ B^2*(P z)^2
    rw [abs_of_nonneg (sq_nonneg (W z*P z))]
    exact hb z
  refine ⟨(memLp_two_iff_integrable_sq
    (hW.aestronglyMeasurable.mul hP.aestronglyMeasurable)).mpr hw,?_⟩
  have hh:=integral_mono hw (hi.const_mul (B^2)) hb
  simpa only [integral_const_mul] using hh

/-- This is the actual four-factor mobility of one continuous background,
with no independent per-leg source or reset of the spatial position. -/
def mobilitySection {R : ℝ} (N : Section R) (z : History) : ℝ :=
  Collision.mobility (fun i=>leg N i z)

theorem mobilitySection_measurable {R : ℝ} (N : Section R) : Measurable (mobilitySection N) :=
  (((leg_evaluate_measurable N 0).mul (leg_evaluate_measurable N 1)).mul
    (leg_evaluate_measurable N 2)).mul (leg_evaluate_measurable N 3)

theorem mobilitySection_bound {R : ℝ} (N : Section R) (z : History) :
    |mobilitySection N z| ≤ ‖N‖^4 := by
  unfold mobilitySection Collision.mobility leg
  simp only [abs_mul]
  have h:=mul_le_mul
    (mul_le_mul (mul_le_mul (evaluate_bound N z.1 (z.2 0)) (evaluate_bound N z.1 (z.2 1))
      (abs_nonneg _) (norm_nonneg N)) (evaluate_bound N z.1 (z.2 2)) (abs_nonneg _)
      (mul_nonneg (norm_nonneg N) (norm_nonneg N)))
    (evaluate_bound N z.1 (z.2 3)) (abs_nonneg _)
    (mul_nonneg (mul_nonneg (norm_nonneg N) (norm_nonneg N)) (norm_nonneg N))
  simpa only [show ‖N‖*‖N‖*‖N‖*‖N‖=‖N‖^4 by ring] using h

theorem actual_weighted_full_test {R : ℝ} (hR : 0 ≤ R) {θ : Thermodynamics.Parameter}
    (hθ : θ∈Thermodynamics.positiveDomain R) (h : Section R) {P W : History→ℝ}
    (hP : MemLp P 2 (volume.prod (jointMeasure R θ))) (hW : Measurable W)
    {B E : ℝ} (hB : 0 ≤ B) (hWbound : ∀z,|W z| ≤ B)
    (hE : (∫z,(P z)^2∂volume.prod (jointMeasure R θ)) ≤ E) :
    (∀i:Fin 4,Integrable (fun z=>W z*P z*leg h i z) (volume.prod (jointMeasure R θ))) ∧
    Integrable (fun z=>W z*P z*fullDifference h z) (volume.prod (jointMeasure R θ)) ∧
    |∫z,W z*P z*fullDifference h z∂volume.prod (jointMeasure R θ)| ≤
      4*B*Real.sqrt E*Real.sqrt (∫k,sectionMass h k∂marginal R θ) := by
  have hw:=bounded_weight_memLp hP hW hWbound
  have hd:=actual_full_test_pairing hR hθ h hw.1
  refine ⟨hd.1,hd.2.1,?_⟩
  have hb:=Real.sqrt_le_sqrt (hw.2.trans (mul_le_mul_of_nonneg_left hE (sq_nonneg B)))
  rw [Real.sqrt_mul (sq_nonneg B),Real.sqrt_sq hB] at hb
  have hh:=mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hb (by norm_num : (0:ℝ)≤4))
    (Real.sqrt_nonneg (∫k,sectionMass h k∂marginal R θ))
  exact hd.2.2.trans (by nlinarith [hh])

def pairCurrent {R : ℝ} (f g : Section R) (a b : Fin 4) (z : History) : ℝ :=
  leg f a z*leg g b z

def tripleCurrent {R : ℝ} (f g h : Section R) (a b d : Fin 4) (z : History) : ℝ :=
  leg f a z*leg g b z*leg h d z

theorem pairCurrent_memLp {R : ℝ} (hR : 0 ≤ R) {θ : Thermodynamics.Parameter}
    (hθ : θ∈Thermodynamics.positiveDomain R) (f g : Section R) (a b : Fin 4) :
    MemLp (pairCurrent f g a b) 2 (volume.prod (jointMeasure R θ)) :=
  (memLp_two_iff_integrable_sq ((leg_evaluate_measurable f a).mul
    (leg_evaluate_measurable g b)).aestronglyMeasurable).mpr
      (ActualTwoOneFullMoser.uncutPairSquare_integrable hR hθ f g a b)

theorem tripleCurrent_memLp {R : ℝ} (hR : 0 ≤ R) {θ : Thermodynamics.Parameter}
    (hθ : θ∈Thermodynamics.positiveDomain R) (f g h : Section R) (a b d : Fin 4) :
    MemLp (tripleCurrent f g h a b d) 2 (volume.prod (jointMeasure R θ)) :=
  (memLp_two_iff_integrable_sq (((leg_evaluate_measurable f a).mul
    (leg_evaluate_measurable g b)).mul (leg_evaluate_measurable h d)).aestronglyMeasurable).mpr
      (ActualThreeFullMoser.uncutTripleSquare_integrable hR hθ f g h a b d)

/-- The physical one-quarter prefactor is retained: its factor cancels
the four-leg Cauchy constant, not any source or test parent. -/
theorem actual_mobility_quarter_pairing {R : ℝ} (hR : 0 ≤ R) {θ : Thermodynamics.Parameter}
    (hθ : θ∈Thermodynamics.positiveDomain R) (N h : Section R) {P : History→ℝ}
    (hP : MemLp P 2 (volume.prod (jointMeasure R θ))) {E : ℝ}
    (hE : (∫z,(P z)^2∂volume.prod (jointMeasure R θ)) ≤ E) :
    (∀i:Fin 4,Integrable (fun z=>mobilitySection N z*P z*leg h i z)
      (volume.prod (jointMeasure R θ))) ∧
    Integrable (fun z=>mobilitySection N z*P z*fullDifference h z)
      (volume.prod (jointMeasure R θ)) ∧
    |(1/4:ℝ)*(∫z,mobilitySection N z*P z*fullDifference h z∂volume.prod (jointMeasure R θ))| ≤
      ‖N‖^4*Real.sqrt E*Real.sqrt (∫k,sectionMass h k∂marginal R θ) := by
  have hd:=actual_weighted_full_test hR hθ h hP (mobilitySection_measurable N)
    (by positivity : 0 ≤ ‖N‖^4) (mobilitySection_bound N) hE
  refine ⟨hd.1,hd.2.1,?_⟩
  rw [abs_mul]
  norm_num
  nlinarith [hd.2.2]

open SpatialJetSpace CornerPairTruncation SpatialProductGN

theorem actual_second_mobility_reader {R : ℝ} (hR : 0 ≤ R) {θ : Thermodynamics.Parameter}
    (hθ : θ∈Thermodynamics.positiveDomain R) (p : JetSpace R) (N h : Section R)
    (a b : Fin 4) (hab : a≠b) (i j : Fin 3) (η : ℝ) {κ M : ℝ}
    (hκ : 0 ≤ κ) (hM : 0 ≤ M) (hp : ∀k,amplitude p k ≤ M)
    (hbulk : ∀k,cut R η k=0 → amplitude p k ≤ κ) :
    let P:=pairCurrent (firstCubeSection p i) (firstCubeSection p j) a b
    (∀d:Fin 4,Integrable (fun z=>mobilitySection N z*P z*leg h d z)
      (volume.prod (jointMeasure R θ))) ∧
    Integrable (fun z=>mobilitySection N z*P z*fullDifference h z)
      (volume.prod (jointMeasure R θ)) ∧
    |(1/4:ℝ)*(∫z,mobilitySection N z*P z*fullDifference h z∂volume.prod (jointMeasure R θ))| ≤
      ‖N‖^4*Real.sqrt ((18*κ*M+9*M^2*omega R θ η)*
        (∫k,SecondSpatialMassGN.mass2 p k∂marginal R θ))*
          Real.sqrt (∫k,sectionMass h k∂marginal R θ) :=
  actual_mobility_quarter_pairing hR hθ N h (pairCurrent_memLp hR hθ _ _ a b)
    (ActualSecondFullMoser.actual_full_second_moser hR hθ p a b hab i j η hκ hM hp hbulk)

theorem actual_two_one_mobility_reader {R : ℝ} (hR : 0 ≤ R) {θ : Thermodynamics.Parameter}
    (hθ : θ∈Thermodynamics.positiveDomain R) (p : JetSpace R) (N h : Section R)
    (a b : Fin 4) (hab : a≠b) (i j n : Fin 3) (η : ℝ) {κ M : ℝ}
    (hκ : 0 ≤ κ) (hM : 0 ≤ M) (hp : ∀k,amplitude p k ≤ M)
    (hbulk : ∀k,cut R η k=0 → amplitude p k ≤ κ) :
    let P:=pairCurrent (secondCubeSection p i j) (firstCubeSection p n) a b
    (∀d:Fin 4,Integrable (fun z=>mobilitySection N z*P z*leg h d z)
      (volume.prod (jointMeasure R θ))) ∧
    Integrable (fun z=>mobilitySection N z*P z*fullDifference h z)
      (volume.prod (jointMeasure R θ)) ∧
    |(1/4:ℝ)*(∫z,mobilitySection N z*P z*fullDifference h z∂volume.prod (jointMeasure R θ))| ≤
      ‖N‖^4*Real.sqrt ((ActualTwoOneFullMoser.smallConstant κ M+
        twoOneConstant M*(omega R θ η)^((2:ℝ)/3))*(∫k,mass p k∂marginal R θ))*
          Real.sqrt (∫k,sectionMass h k∂marginal R θ) :=
  actual_mobility_quarter_pairing hR hθ N h (pairCurrent_memLp hR hθ _ _ a b)
    (ActualTwoOneFullMoser.actual_full_two_one_moser hR hθ p a b hab i j n η hκ hM hp hbulk)

theorem actual_three_mobility_reader {R : ℝ} (hR : 0 ≤ R) {θ : Thermodynamics.Parameter}
    (hθ : θ∈Thermodynamics.positiveDomain R) (p : JetSpace R) (N h : Section R)
    (a b d : Fin 4) (hab : a≠b) (i j n : Fin 3) (η : ℝ) {κ M : ℝ}
    (hp : ∀k,amplitude p k ≤ M) (hbulk : ∀k,cut R η k=0 → amplitude p k ≤ κ) :
    let P:=tripleCurrent (firstCubeSection p i) (firstCubeSection p j) (firstCubeSection p n) a b d
    (∀e:Fin 4,Integrable (fun z=>mobilitySection N z*P z*leg h e z)
      (volume.prod (jointMeasure R θ))) ∧
    Integrable (fun z=>mobilitySection N z*P z*fullDifference h z)
      (volume.prod (jointMeasure R θ)) ∧
    |(1/4:ℝ)*(∫z,mobilitySection N z*P z*fullDifference h z∂volume.prod (jointMeasure R θ))| ≤
      ‖N‖^4*Real.sqrt ((ActualThreeFullMoser.threeSmallConstant κ M+
        2500*M^4*(omega R θ η)^((2:ℝ)/3))*(∫k,mass p k∂marginal R θ))*
          Real.sqrt (∫k,sectionMass h k∂marginal R θ) :=
  actual_mobility_quarter_pairing hR hθ N h (tripleCurrent_memLp hR hθ _ _ _ a b d)
    (ActualThreeFullMoser.actual_full_three_moser hR hθ p a b d hab i j n η hp hbulk)

end
end Resonance.JointEnergyReader
