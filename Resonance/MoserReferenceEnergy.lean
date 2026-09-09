import Resonance.JointEnergyReader
import Resonance.ContinuousWeightedEnergy

/-! The mixed-quartet estimates are read in the manuscript's one fixed
H_nu space. Its frequency, measure, and continuous representatives are
those already constructed from the same physical sharp-cube collision. -/
open Set MeasureTheory
open scoped ENNReal
namespace Resonance.MoserReferenceEnergy
noncomputable section
open ResonantMeasure WeightedJointMeasure FrequencyWeightedForm FreeTransport
open SpatialIntegrationByParts SpatialMomentumSections JointEnergyReader
open SpatialJetSpace MixedSpatialGN SecondSpatialMassGN ReferenceFrequencySpace
open ContinuousWeightedEnergy JointWeightComparison
set_option maxHeartbeats 1800000

def spatialSlice {R : ℝ} (h : Section R) (X : SpatialTorus) :
    ContinuousWeightedEnergy.CubeFunction R :=
  ⟨fun k=>h k X,by fun_prop⟩

theorem toWeighted_slice_ae {R : ℝ} (hR : 0 < R) (h : Section R) (X : SpatialTorus) :
    (toWeighted hR (spatialSlice h X):E→ℝ)=ᵐ[referenceMeasure R](fun k=>evaluate h X k) := by
  have hu:=(ReferenceFrequencySpace.reference_volume_equivalent hR).2.ae_le
    (toWeighted_ae hR (spatialSlice h X))
  filter_upwards [hu,reference_support R] with k hk hcube
  rw [hk,FiberContinuity.continuousExtension_eq R (spatialSlice h X) ⟨k,hcube⟩,
    show evaluate h X k=h ⟨k,hcube⟩ X from evaluate_on h X ⟨k,hcube⟩]
  rfl

theorem toWeighted_slice_norm {R : ℝ} (hR : 0 < R) (h : Section R) (X : SpatialTorus) :
    ‖toWeighted hR (spatialSlice h X)‖^2 = ∫k,(evaluate h X k)^2∂referenceMeasure R := by
  rw [←real_inner_self_eq_norm_sq,L2.inner_def]
  apply integral_congr_ae
  filter_upwards [toWeighted_slice_ae hR h X] with k hk
  change (toWeighted hR (spatialSlice h X) k)*(toWeighted hR (spatialSlice h X) k)=_
  rw [hk,pow_two]

theorem actual_reference_section_identity {R : ℝ} (hR : 0 < R) (h : Section R) :
    Integrable (fun X=>‖toWeighted hR (spatialSlice h X)‖^2) (volume:Measure SpatialTorus) ∧
    (∫k,sectionMass h k∂referenceMeasure R)=
      ∫X,‖toWeighted hR (spatialSlice h X)‖^2 := by
  letI:=PhysicalFiveBasis.reference_finite hR.le
  have hi:=evaluate_square_integrable h (referenceMeasure R)
  constructor
  · apply hi.integral_prod_left.congr
    exact ae_of_all _ (fun X=>(toWeighted_slice_norm hR h X).symm)
  · have h1:=integral_prod _ hi
    have h2:=integral_prod_symm _ hi
    change (∫k,(∫X,(evaluate h X k)^2)∂referenceMeasure R)=_
    rw [←h2,h1]
    apply integral_congr_ae
    exact ae_of_all _ (fun X=>(toWeighted_slice_norm hR h X).symm)

def referenceEnergy3 {R : ℝ} (hR : 0 < R) (p : JetSpace R) : ℝ :=
  ∑i:Fin 3,∑j:Fin 3,∑l:Fin 3,∫X,
    ‖toWeighted hR (spatialSlice (thirdCubeSection p i j l) X)‖^2

def referenceEnergy2 {R : ℝ} (hR : 0 < R) (p : JetSpace R) : ℝ :=
  ∑i:Fin 3,∑j:Fin 3,∫X,
    ‖toWeighted hR (spatialSlice (secondCubeSection p i j) X)‖^2

theorem third_mass_sum (p : JetSpace R) (k : E) :
    mass p k=∑i:Fin 3,∑j:Fin 3,∑l:Fin 3,sectionMass (thirdCubeSection p i j l) k := by
  rw [mass_integral_identity]
  have hi (i j l:Fin 3) : Integrable (fun X:SpatialTorus=>(evaluate (thirdCubeSection p i j l) X k)^2)
      (volume:Measure SpatialTorus) := scalar_integrable ((zeroSection (thirdCubeSection p i j l) k)^2)
  rw [integral_finset_sum _ (fun i _=>integrable_finset_sum _ (fun j _=>
    integrable_finset_sum _ (fun l _=>hi i j l)))]
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_finset_sum _ (fun j _=>integrable_finset_sum _ (fun l _=>
    hi i j l))]
  apply Finset.sum_congr rfl
  intro j _
  exact integral_finset_sum _ (fun l _=>hi i j l)

theorem second_mass_sum (p : JetSpace R) (k : E) :
    mass2 p k=∑i:Fin 3,∑j:Fin 3,sectionMass (secondCubeSection p i j) k := by
  rw [mass2_integral_identity]
  have hi (i j:Fin 3) : Integrable (fun X:SpatialTorus=>(evaluate (secondCubeSection p i j) X k)^2)
      (volume:Measure SpatialTorus) := scalar_integrable ((zeroSection (secondCubeSection p i j) k)^2)
  rw [integral_finset_sum _ (fun i _=>integrable_finset_sum _ (fun j _=>
    hi i j))]
  apply Finset.sum_congr rfl
  intro i _
  exact integral_finset_sum _ (fun j _=>hi i j)

theorem actual_third_reference_mass {R : ℝ} (hR : 0 < R) (p : JetSpace R) :
    (∫k,mass p k∂referenceMeasure R)=referenceEnergy3 hR p := by
  letI:=PhysicalFiveBasis.reference_finite hR.le
  simp_rw [third_mass_sum]
  rw [integral_finset_sum _ (fun i _=>integrable_finset_sum _ (fun j _=>
    integrable_finset_sum _ (fun l _=>sectionMass_integrable (thirdCubeSection p i j l) _)))]
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_finset_sum _ (fun j _=>integrable_finset_sum _ (fun l _=>
    sectionMass_integrable (thirdCubeSection p i j l) _))]
  apply Finset.sum_congr rfl
  intro j _
  rw [integral_finset_sum _ (fun l _=>sectionMass_integrable (thirdCubeSection p i j l) _)]
  apply Finset.sum_congr rfl
  intro l _
  exact (actual_reference_section_identity hR _).2

theorem actual_second_reference_mass {R : ℝ} (hR : 0 < R) (p : JetSpace R) :
    (∫k,mass2 p k∂referenceMeasure R)=referenceEnergy2 hR p := by
  letI:=PhysicalFiveBasis.reference_finite hR.le
  simp_rw [second_mass_sum]
  rw [integral_finset_sum _ (fun i _=>integrable_finset_sum _ (fun j _=>
    sectionMass_integrable (secondCubeSection p i j) _))]
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_finset_sum _ (fun j _=>sectionMass_integrable (secondCubeSection p i j) _)]
  apply Finset.sum_congr rfl
  intro j _
  exact (actual_reference_section_identity hR _).2

def referenceCost (R : ℝ) : ℝ := (inverseLowerFactor R).toReal

theorem unit_third_mass_bound {R : ℝ} (hR : 0 < R) (p : JetSpace R) :
    (∫k,mass p k∂marginal R unitParameter) ≤ referenceCost R*referenceEnergy3 hR p := by
  letI:=PhysicalFiveBasis.reference_finite hR.le
  have hi:=(mass_integrable p (referenceMeasure R)).smul_measure (inverseLowerFactor_finite R)
  have hb:=integral_mono_measure (unit_le_reference hR.le)
    (ae_of_all _ (mass_nonnegative p)) hi
  rw [integral_smul_measure,smul_eq_mul,actual_third_reference_mass hR p] at hb
  exact hb

theorem unit_second_mass_bound {R : ℝ} (hR : 0 < R) (p : JetSpace R) :
    (∫k,mass2 p k∂marginal R unitParameter) ≤ referenceCost R*referenceEnergy2 hR p := by
  letI:=PhysicalFiveBasis.reference_finite hR.le
  have hi:=(mass2_integrable p (referenceMeasure R)).smul_measure (inverseLowerFactor_finite R)
  have hb:=integral_mono_measure (unit_le_reference hR.le)
    (ae_of_all _ (mass2_nonnegative p)) hi
  rw [integral_smul_measure,smul_eq_mul,actual_second_reference_mass hR p] at hb
  exact hb

theorem unit_section_mass_bound {R : ℝ} (hR : 0 < R) (h : Section R) :
    (∫k,sectionMass h k∂marginal R unitParameter) ≤
      referenceCost R*(∫X,‖toWeighted hR (spatialSlice h X)‖^2) := by
  letI:=PhysicalFiveBasis.reference_finite hR.le
  have hi:=(sectionMass_integrable h (referenceMeasure R)).smul_measure (inverseLowerFactor_finite R)
  have hb:=integral_mono_measure (unit_le_reference hR.le)
    (ae_of_all _ (sectionMass_nonnegative h)) hi
  rw [integral_smul_measure,smul_eq_mul,(actual_reference_section_identity hR h).2] at hb
  exact hb

theorem actual_third_Hnu_moser {R : ℝ} (hR : 0 < R) (p : JetSpace R)
    (a b : Fin 4) (hab : a≠b) (i j n : Fin 3) (η : ℝ) {κ M : ℝ}
    (hκ : 0 ≤ κ) (hM : 0 ≤ M) (hp : ∀k,amplitude p k ≤ M)
    (hbulk : ∀k,CornerPairTruncation.cut R η k=0 → amplitude p k ≤ κ) :
    (∫z,(pairCurrent (secondCubeSection p i j) (firstCubeSection p n) a b z)^2
      ∂volume.prod (pairingMeasure R)) ≤
      (ActualTwoOneFullMoser.smallConstant κ M+
        SpatialProductGN.twoOneConstant M*(CornerPairTruncation.omega R unitParameter η)^((2:ℝ)/3))*
          referenceCost R*referenceEnergy3 hR p := by
  have hb:=ActualTwoOneFullMoser.actual_full_two_one_moser hR.le (unitParameter_positive R)
    p a b hab i j n η hκ hM hp hbulk
  rw [unit_joint] at hb
  have hz : 0 ≤ ActualTwoOneFullMoser.smallConstant κ M+
      SpatialProductGN.twoOneConstant M*(CornerPairTruncation.omega R unitParameter η)^((2:ℝ)/3) := by
    have hω:=CornerPairTruncation.omega_nonnegative R unitParameter η
    exact add_nonneg (add_nonneg (ActualTwoOneFullMoser.mixedConstant_nonnegative hκ)
      (ActualTwoOneFullMoser.mixedConstant_nonnegative hM))
      (mul_nonneg (SpatialProductGN.twoOneConstant_nonneg hM) (by positivity))
  have hh:=mul_le_mul_of_nonneg_left (unit_third_mass_bound hR p) hz
  exact hb.trans (by nlinarith [hh])

theorem actual_second_Hnu_moser {R : ℝ} (hR : 0 < R) (p : JetSpace R)
    (a b : Fin 4) (hab : a≠b) (i j : Fin 3) (η : ℝ) {κ M : ℝ}
    (hκ : 0 ≤ κ) (hM : 0 ≤ M) (hp : ∀k,amplitude p k ≤ M)
    (hbulk : ∀k,CornerPairTruncation.cut R η k=0 → amplitude p k ≤ κ) :
    (∫z,(pairCurrent (firstCubeSection p i) (firstCubeSection p j) a b z)^2
      ∂volume.prod (pairingMeasure R)) ≤
      (18*κ*M+9*M^2*CornerPairTruncation.omega R unitParameter η)*
        referenceCost R*referenceEnergy2 hR p := by
  have hb:=ActualSecondFullMoser.actual_full_second_moser hR.le (unitParameter_positive R)
    p a b hab i j η hκ hM hp hbulk
  rw [unit_joint] at hb
  have hz : 0 ≤ 18*κ*M+9*M^2*CornerPairTruncation.omega R unitParameter η := by
    have hω:=CornerPairTruncation.omega_nonnegative R unitParameter η
    positivity
  have hh:=mul_le_mul_of_nonneg_left (unit_second_mass_bound hR p) hz
  exact hb.trans (by nlinarith [hh])

theorem actual_three_Hnu_moser {R : ℝ} (hR : 0 < R) (p : JetSpace R)
    (a b d : Fin 4) (hab : a≠b) (i j n : Fin 3) (η : ℝ) {κ M : ℝ}
    (hp : ∀k,amplitude p k ≤ M)
    (hbulk : ∀k,CornerPairTruncation.cut R η k=0 → amplitude p k ≤ κ) :
    (∫z,(tripleCurrent (firstCubeSection p i) (firstCubeSection p j) (firstCubeSection p n) a b d z)^2
      ∂volume.prod (pairingMeasure R)) ≤
      (ActualThreeFullMoser.threeSmallConstant κ M+
        2500*M^4*(CornerPairTruncation.omega R unitParameter η)^((2:ℝ)/3))*
          referenceCost R*referenceEnergy3 hR p := by
  have hb:=ActualThreeFullMoser.actual_full_three_moser hR.le (unitParameter_positive R)
    p a b d hab i j n η hp hbulk
  rw [unit_joint] at hb
  have hz : 0 ≤ ActualThreeFullMoser.threeSmallConstant κ M+
      2500*M^4*(CornerPairTruncation.omega R unitParameter η)^((2:ℝ)/3) := by
    have hω:=CornerPairTruncation.omega_nonnegative R unitParameter η
    unfold ActualThreeFullMoser.threeSmallConstant
    exact add_nonneg (add_nonneg (add_nonneg
      (ActualThreeFullMoser.threeConstant_nonnegative _ _ _)
      (ActualThreeFullMoser.threeConstant_nonnegative _ _ _))
      (ActualThreeFullMoser.threeConstant_nonnegative _ _ _)) (by positivity)
  have hh:=mul_le_mul_of_nonneg_left (unit_third_mass_bound hR p) hz
  exact hb.trans (by nlinarith [hh])

end
end Resonance.MoserReferenceEnergy
