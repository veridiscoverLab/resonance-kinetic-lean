import Resonance.CrossPairMarginal

/-! The actual incoming--outgoing pair (k₀,k₂), obtained from the same
relative rectangle by a volume-preserving shear. -/
open MeasureTheory Set
open scoped ENNReal
namespace Resonance.CrossPairCoordinates
noncomputable section
open ResonantMeasure CrossPairMarginal
open PlaneCoarea (E2)

def pairCoordinates (p : E×(E×E2)) : (E×E)×E2 :=
  ((p.1,p.1+p.2.1),p.2.2)

abbrev pairPlaneVolume : Measure ((E×E)×E2) :=
  ((volume : Measure E).prod (volume : Measure E)).prod (volume : Measure E2)

theorem pairCoordinates_preserving : MeasurePreserving pairCoordinates
    ((volume : Measure E).prod ((volume : Measure E).prod (volume : Measure E2)))
    pairPlaneVolume := by
  have h₁ := MeasurePreserving.symm MeasurableEquiv.prodAssoc
    (measurePreserving_prodAssoc (volume : Measure E) (volume : Measure E) (volume : Measure E2))
  have h₂ := (measurePreserving_prod_add (volume : Measure E) (volume : Measure E)).prod
    (MeasurePreserving.id (volume : Measure E2))
  exact h₂.comp h₁

def crossQuartet (p : (E×E)×E2) : FourMomenta :=
  relativeQuartet (p.1.1,(p.1.2-p.1.1,p.2))

theorem crossQuartet_measurable : Measurable crossQuartet := by
  have hm : Measurable (fun p : (E×E)×E2=>(p.1.1,(p.1.2-p.1.1,p.2))) := by fun_prop
  exact relativeQuartet_measurable.comp hm

theorem crossQuartet_pairCoordinates (p : E×(E×E2)) :
    crossQuartet (pairCoordinates p)=relativeQuartet p := by
  simp only [crossQuartet,pairCoordinates,add_sub_cancel_left]

theorem pairCoordinates_difference (p : E×(E×E2)) :
    (pairCoordinates p).1.2-(pairCoordinates p).1.1=p.2.1 := by
  simp only [pairCoordinates,add_sub_cancel_left]

theorem crossQuartet_first (p : (E×E)×E2) : crossQuartet p 0=p.1.1 := rfl
theorem crossQuartet_third (p : (E×E)×E2) : crossQuartet p 2=p.1.2 := by
  change p.1.1+(p.1.2-p.1.1)=p.1.2
  abel

theorem relative_cross_lintegral (Φ : FourMomenta→ℝ≥0∞) (hΦ : Measurable Φ) :
    (∫⁻ p,ENNReal.ofReal (‖p.2.1‖⁻¹)*Φ (relativeQuartet p)
      ∂((volume : Measure E).prod ((volume : Measure E).prod (volume : Measure E2))))=
    ∫⁻ p,ENNReal.ofReal (‖p.1.2-p.1.1‖⁻¹)*Φ (crossQuartet p) ∂pairPlaneVolume := by
  have hm : Measurable (fun p : (E×E)×E2=>
      ENNReal.ofReal (‖p.1.2-p.1.1‖⁻¹)*Φ (crossQuartet p)) :=
    (show Measurable (fun p : (E×E)×E2=>ENNReal.ofReal (‖p.1.2-p.1.1‖⁻¹)) by fun_prop).mul
      (hΦ.comp crossQuartet_measurable)
  have h := pairCoordinates_preserving.lintegral_comp hm
  simpa only [pairCoordinates_difference,crossQuartet_pairCoordinates] using h

theorem pairing_cross_lintegral {R : ℝ} (hR : 0≤R) (Φ : FourMomenta→ℝ≥0∞)
    (hΦ : Measurable Φ) :
    (∫⁻ q,Φ q∂pairingMeasure R)=
    (1/2 : ℝ≥0∞)*∫⁻ p,ENNReal.ofReal (‖p.1.2-p.1.1‖⁻¹)*
      (CoareaNormalization.allFourFlags R).indicator Φ (crossQuartet p) ∂pairPlaneVolume := by
  let ψ := (CoareaNormalization.allFourFlags R).indicator Φ
  have hψ : Measurable ψ := hΦ.indicator (CoareaNormalization.allFourFlags_measurable R)
  have hi : (fun p : PlaneGlobal.PlaneParameters=>
      (PlaneGlobal.planeAllowed R).indicator (fun p=>Φ (PlaneGlobal.planeShell p 0)) p)=
      fun p=>ψ (PlaneGlobal.planeShell p 0) := by
    funext p
    by_cases hp : p∈PlaneGlobal.planeAllowed R
    · have hq : PlaneGlobal.planeShell p 0∈CoareaNormalization.allFourFlags R := hp
      simp only [Set.indicator_of_mem hp,ψ,Set.indicator_of_mem hq]
    · have hq : PlaneGlobal.planeShell p 0∉CoareaNormalization.allFourFlags R := hp
      simp only [Set.indicator_of_notMem hp,ψ,Set.indicator_of_notMem hq]
  rw [←PlaneGlobal.planeMeasure_eq_pairingMeasure hR,PlaneGlobal.planeMeasure,
    lintegral_map hΦ PlaneGlobal.planeShell_zero_measurable,PlaneGlobal.planeParameterMeasure,
    lintegral_smul_measure,smul_eq_mul,
    ←lintegral_indicator (PlaneGlobal.planeAllowed_measurable R),hi,
    planeBase_relative_lintegral ψ hψ,relative_cross_lintegral ψ hψ]

end
end Resonance.CrossPairCoordinates
