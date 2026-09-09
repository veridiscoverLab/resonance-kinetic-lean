import Resonance.PairCoordinates

/-! Coordinates for the actual incoming pair marginal of the complete
quartet.  The outgoing sphere, the common center, and all sharp flags
remain in the same integrand throughout the change of variables. -/
open MeasureTheory Set
open scoped ENNReal
namespace Resonance.IncomingPairMarginal
noncomputable section
open ResonantMeasure PairCoordinates
open PolarCoordinates (polarBase polarVector_preserves_volume base_from_polarBase)

def cartesianSphere (p : Parameters) : (E×E)×Sphere :=
  ((p.1,(p.2.1 : ℝ) • (p.2.2.1 : E)),p.2.2.2)

theorem cartesianSphere_preserving : MeasurePreserving cartesianSphere polarBase
    (((volume : Measure E).prod volume).prod surface) := by
  let m := Measure.volumeIoiPow 2
  letI : SigmaFinite m := inferInstanceAs (SigmaFinite (Measure.volumeIoiPow 2))
  letI : SigmaFinite (m.prod surface) := inferInstance
  letI : SigmaFinite ((m.prod surface).prod surface) := inferInstance
  have h₁ := (MeasurePreserving.id (volume : Measure E)).prod
    (MeasurePreserving.symm MeasurableEquiv.prodAssoc
      (measurePreserving_prodAssoc m surface surface))
  have h₂ := (MeasurePreserving.id (volume : Measure E)).prod
    ((polarVector_preserves_volume.comp Measure.measurePreserving_swap).prod
      (MeasurePreserving.id surface))
  have h₃ := MeasurePreserving.symm MeasurableEquiv.prodAssoc
    (measurePreserving_prodAssoc (volume : Measure E) (volume : Measure E) surface)
  exact h₃.comp (h₂.comp h₁)

def centerQuartet (p : (E×E)×Sphere) : FourMomenta :=
  ![p.1.1+p.1.2,p.1.1-p.1.2,
    p.1.1+‖p.1.2‖ • (p.2 : E),p.1.1-‖p.1.2‖ • (p.2 : E)]

theorem centerQuartet_measurable : Measurable centerQuartet := by
  apply measurable_pi_lambda
  intro i
  fin_cases i <;> dsimp [centerQuartet] <;> fun_prop

theorem cartesianSphere_radius (p : Parameters) : ‖(cartesianSphere p).1.2‖=(p.2.1 : ℝ) := by
  have hr : 0 < (p.2.1 : ℝ) := p.2.1.property
  simp [cartesianSphere,norm_smul,abs_of_pos hr]

theorem centerQuartet_parameters (p : Parameters) : centerQuartet (cartesianSphere p)=paired p := by
  rw [centerQuartet,cartesianSphere_radius]
  rfl

def incomingQuartet (p : (E×E)×Sphere) : FourMomenta :=
  ![p.1.1,p.1.2,(1/2 : ℝ) • (p.1.1+p.1.2)+(‖p.1.1-p.1.2‖/2) • (p.2 : E),
    (1/2 : ℝ) • (p.1.1+p.1.2)-(‖p.1.1-p.1.2‖/2) • (p.2 : E)]

theorem incomingQuartet_measurable : Measurable incomingQuartet := by
  apply measurable_pi_lambda
  intro i
  fin_cases i <;> dsimp [incomingQuartet] <;> fun_prop

theorem pairMap_relative_norm (p : E×E) : ‖(pairMap p).1-(pairMap p).2‖/2=‖p.2‖ := by
  have he : (pairMap p).1-(pairMap p).2=(2 : ℝ) • p.2 := by
    simp only [pairMap,two_smul]
    abel
  rw [he,norm_smul]
  norm_num

theorem incomingQuartet_pairMap (p : (E×E)×Sphere) :
    incomingQuartet (pairMap p.1,p.2)=centerQuartet p := by
  have hc : (1/2 : ℝ) • ((pairMap p.1).1+(pairMap p.1).2)=p.1.1 := by
    simp only [pairMap,smul_add,smul_sub]
    module
  funext i
  fin_cases i
  · rfl
  · rfl
  · change (1/2 : ℝ) • ((pairMap p.1).1+(pairMap p.1).2) +
      (‖(pairMap p.1).1-(pairMap p.1).2‖/2) • (p.2 : E) =
        p.1.1+‖p.1.2‖ • (p.2 : E)
    rw [hc,pairMap_relative_norm]
  · change (1/2 : ℝ) • ((pairMap p.1).1+(pairMap p.1).2) -
      (‖(pairMap p.1).1-(pairMap p.1).2‖/2) • (p.2 : E) =
        p.1.1-‖p.1.2‖ • (p.2 : E)
    rw [hc,pairMap_relative_norm]

abbrev pairSphereVolume : Measure ((E×E)×Sphere) :=
  ((volume : Measure E).prod volume).prod surface

theorem base_cartesian_lintegral (Φ : FourMomenta→ℝ≥0∞) (hΦ : Measurable Φ) :
    (∫⁻ p, Φ (paired p) ∂base) =
      ∫⁻ p, ENNReal.ofReal ‖p.1.2‖ * Φ (centerQuartet p) ∂pairSphereVolume := by
  rw [base_from_polarBase]
  have hwd := lintegral_withDensity_eq_lintegral_mul polarBase
    (f := fun p : Parameters => ENNReal.ofReal (p.2.1 : ℝ)) (by fun_prop)
    (g := fun p => Φ (paired p)) (hΦ.comp continuous_paired.measurable)
  rw [hwd]
  have h := cartesianSphere_preserving.lintegral_comp
    ((show Measurable (fun p : (E×E)×Sphere => ENNReal.ofReal ‖p.1.2‖) by fun_prop).mul
      (hΦ.comp centerQuartet_measurable))
  simpa only [Pi.mul_apply,Function.comp_def,cartesianSphere_radius,centerQuartet_parameters] using h

theorem pairSphereMap_volume :
    Measure.map (Prod.map pairMap (id : Sphere→Sphere)) pairSphereVolume =
      ENNReal.ofReal (1/8 : ℝ) • pairSphereVolume := by
  rw [←Measure.map_prod_map _ _ pairMap_measurable measurable_id,
    pairMap_volume,Measure.map_id,Measure.prod_smul_left]

theorem cartesian_incoming_lintegral (Φ : FourMomenta→ℝ≥0∞) (hΦ : Measurable Φ) :
    (∫⁻ p, ENNReal.ofReal ‖p.1.2‖ * Φ (centerQuartet p) ∂pairSphereVolume) =
      ENNReal.ofReal (1/8 : ℝ) *
        ∫⁻ p, ENNReal.ofReal (‖p.1.1-p.1.2‖/2) * Φ (incomingQuartet p)
          ∂pairSphereVolume := by
  have hm : Measurable (fun p : (E×E)×Sphere =>
      ENNReal.ofReal (‖p.1.1-p.1.2‖/2) * Φ (incomingQuartet p)) :=
    (show Measurable (fun p : (E×E)×Sphere => ENNReal.ofReal (‖p.1.1-p.1.2‖/2))
      by fun_prop).mul (hΦ.comp incomingQuartet_measurable)
  have h := lintegral_map (μ := pairSphereVolume) hm (pairMap_measurable.prodMap measurable_id)
  rw [pairSphereMap_volume,lintegral_smul_measure] at h
  simpa only [Prod.map,Function.id_def,smul_eq_mul,pairMap_relative_norm,incomingQuartet_pairMap]
    using h.symm

theorem pairing_incoming_lintegral (R : ℝ) (Φ : FourMomenta→ℝ≥0∞)
    (hΦ : Measurable Φ) :
    (∫⁻ q, Φ q ∂pairingMeasure R) =
      ∫⁻ p, ENNReal.ofReal (‖p.1.1-p.1.2‖/8) *
        (CoareaNormalization.allFourFlags R).indicator Φ (incomingQuartet p)
        ∂pairSphereVolume := by
  let ψ := (CoareaNormalization.allFourFlags R).indicator Φ
  have hψ : Measurable ψ := hΦ.indicator (CoareaNormalization.allFourFlags_measurable R)
  have hi : (fun p : Parameters => (allowed R).indicator (fun p => Φ (paired p)) p) =
      fun p => ψ (paired p) := by
    funext p
    by_cases hp : p∈allowed R
    · have hq : paired p∈CoareaNormalization.allFourFlags R := hp
      simp only [Set.indicator_of_mem hp,ψ,Set.indicator_of_mem hq]
    · have hq : paired p∉CoareaNormalization.allFourFlags R := hp
      simp only [Set.indicator_of_notMem hp,ψ,Set.indicator_of_notMem hq]
  rw [pairingMeasure,lintegral_map hΦ continuous_paired.measurable,
    parameterMeasure,lintegral_smul_measure,smul_eq_mul,
    ←lintegral_indicator (measurable_allowed R),hi,
    base_cartesian_lintegral ψ hψ,cartesian_incoming_lintegral ψ hψ]
  have hm : Measurable (fun p : (E×E)×Sphere =>
      ENNReal.ofReal (‖p.1.1-p.1.2‖/2) * ψ (incomingQuartet p)) :=
    (show Measurable (fun p : (E×E)×Sphere => ENNReal.ofReal (‖p.1.1-p.1.2‖/2))
      by fun_prop).mul (hψ.comp incomingQuartet_measurable)
  rw [←mul_assoc,←lintegral_const_mul _ hm]
  apply lintegral_congr
  intro p
  rw [←mul_assoc]
  congr 1
  have he : (2 : ℝ≥0∞)*ENNReal.ofReal (1/8 : ℝ)=ENNReal.ofReal (1/4 : ℝ) := by
    have htwo : (2 : ℝ≥0∞)=ENNReal.ofReal (2 : ℝ) := by norm_num
    rw [htwo,←ENNReal.ofReal_mul (by norm_num)]
    norm_num
  rw [he,←ENNReal.ofReal_mul (by norm_num)]
  congr 1
  ring

end
end Resonance.IncomingPairMarginal
