import Resonance.SpacetimeContinuousFields

/-! The complete mobility belongs to the same actual distribution. The
variable-reference weight multiplied by the full squared root ratio is
exactly its four-leg mobility measure; no reference or source is refreshed. -/
open Set MeasureTheory MeasureTheory.Measure
open scoped ENNReal
namespace Resonance.SpacetimeActualMobility
noncomputable section
open ResonantMeasure Thermodynamics SpacetimePairing SpacetimeRootMultiplier
open SpacetimeContinuousFields WeightedJointMeasure

def sourceRatio {R : ℝ} (F : Base→C(cube R,ℝ)) (θ : Base→Parameter) (z : Source) : ℝ :=
  field F z/profile (θ z.1) z.2

def actualWeight {R : ℝ} (F : Base→C(cube R,ℝ)) (p : Joint) : ℝ≥0∞ :=
  ENNReal.ofReal (∏i:Fin 4,field F (leg i p))

def actualMeasure {R : ℝ} (T : ℝ) (F : Base→C(cube R,ℝ)) : Measure Joint :=
  (SpacetimePairing.jointMeasure R T).withDensity (actualWeight F)

theorem sourceRatio_measurable {R : ℝ} {F : Base→C(cube R,ℝ)} {θ : Base→Parameter}
    (hF : Measurable F) (hm : Measurable θ) : Measurable (sourceRatio F θ) :=
  (field_measurable hF).div (SpacetimeRJMeasure.joint_profile_measurable.comp
    ((hm.comp measurable_fst).prodMk measurable_snd))

theorem actualWeight_measurable {R : ℝ} (hR : 0≤R) (T : ℝ) {F : Base→C(cube R,ℝ)}
    (hF : Measurable F) : Measurable (actualWeight F) := by
  apply Measurable.ennreal_ofReal
  exact Finset.measurable_prod _ (fun i _=>(field_measurable hF).comp
    (SpacetimePairing.leg_quasiMeasurePreserving hR T i).measurable)

theorem mobility_normalization (f N : Fin 4→ℝ) (hf : ∀i,0≤f i) (hN : ∀i,0<N i) :
    (∏i,N i)*(Real.sqrt (∏i,f i/N i))^2=∏i,f i := by
  rw [Real.sq_sqrt (Finset.prod_nonneg (fun i _=>div_nonneg (hf i) (hN i).le)),
    Finset.prod_div_distrib]
  exact mul_div_cancel₀ _ (ne_of_gt (Finset.prod_pos (fun i _=>hN i)))

theorem normalized_weight_ae {R : ℝ} (T : ℝ) {F : Base→C(cube R,ℝ)} {θ : Base→Parameter}
    (hF : ∀ᵐa∂baseMeasure T,∀k,0≤F a k)
    (hθ : ∀ᵐa∂baseMeasure T,θ a∈positiveDomain R) :
    (fun p=>SpacetimeRJMeasure.weight θ p*ENNReal.ofReal ((root (sourceRatio F θ) p)^2))
      =ᵐ[SpacetimePairing.jointMeasure R T]actualWeight F := by
  filter_upwards [joint_full_support R T,base_property_on_joint R T hF,
    base_property_on_joint R T hθ] with p hp hf ht
  have hf0 (i:Fin 4):0≤field F (leg i p) := by
    change 0≤field F (p.1,p.2 i)
    rw [show field F (p.1,p.2 i)=F p.1 ⟨p.2 i,hp.1 i⟩ from
      field_on_cube F p.1 ⟨p.2 i,hp.1 i⟩]
    exact hf _
  have hN (i:Fin 4):0<profile (θ p.1) (p.2 i):=profile_pos ht (hp.1 i)
  rw [SpacetimeRJMeasure.weight,←ENNReal.ofReal_mul (Finset.prod_pos (fun i _=>hN i)).le]
  apply congrArg ENNReal.ofReal
  exact mobility_normalization (fun i=>field F (leg i p)) (fun i=>profile (θ p.1) (p.2 i)) hf0 hN

theorem actual_mobility_measure {R : ℝ} (hR : 0≤R) (T : ℝ)
    {F : Base→C(cube R,ℝ)} {θ : Base→Parameter}
    (hFm : Measurable F) (hm : Measurable θ)
    (hF : ∀ᵐa∂baseMeasure T,∀k,0≤F a k)
    (hθ : ∀ᵐa∂baseMeasure T,θ a∈positiveDomain R) :
    (SpacetimeRJMeasure.measure R T θ).withDensity
      (fun p=>ENNReal.ofReal ((root (sourceRatio F θ) p)^2))=actualMeasure T F := by
  have hroot:=(root_measurable hR T (sourceRatio_measurable hFm hm).aestronglyMeasurable).pow 2
  erw [SpacetimeRJMeasure.measure,←withDensity_mul₀
    (SpacetimeRJMeasure.weight_measurable hm).aemeasurable hroot.aemeasurable.ennreal_ofReal]
  exact withDensity_congr_ae (normalized_weight_ae T hF hθ)

end
end Resonance.SpacetimeActualMobility
