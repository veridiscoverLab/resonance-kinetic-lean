import Resonance.SpacetimeContinuousFields

/-! Products of the same actual cube families before and after the global
reference-space embedding; all slice representatives are identified. -/
open Set MeasureTheory MeasureTheory.Measure
open scoped ENNReal
namespace Resonance.SpacetimeSourceProducts
noncomputable section
open ResonantMeasure SpacetimePairing SpacetimeReference SpacetimeContinuousFields
open LpOperators ProductL2Slices

theorem family_product_bound {R : ℝ} (T : ℝ) {B F : Base→C(cube R,ℝ)} {CB CF : ℝ}
    (hCB : 0≤CB) (hB : ∀ᵐa∂baseMeasure T,‖B a‖≤CB)
    (hF : ∀ᵐa∂baseMeasure T,‖F a‖≤CF) :
    ∀ᵐa∂baseMeasure T,‖B a*F a‖≤CB*CF := by
  filter_upwards [hB,hF] with a hb hf
  exact (norm_mul_le _ _).trans (mul_le_mul hb hf (norm_nonneg _) hCB)

theorem family_coefficient_memLp {R : ℝ} (T : ℝ) {B : Base→C(cube R,ℝ)} {CB : ℝ}
    (hm : Measurable B) (hB : ∀ᵐa∂baseMeasure T,‖B a‖≤CB) :
    MemLp (field B) ∞ (reference R T) :=
  memLp_top_of_bound (field_measurable hm).aestronglyMeasurable CB (field_reference_bound T hB)

set_option backward.isDefEq.respectTransparency false in
theorem source_product {R : ℝ} (hR : 0≤R) (T : ℝ)
    {B F : Base→C(cube R,ℝ)} {CB CF : ℝ} (hCB : 0≤CB)
    (hBm : Measurable B) (hFm : Measurable F)
    (hB : ∀ᵐa∂baseMeasure T,‖B a‖≤CB) (hF : ∀ᵐa∂baseMeasure T,‖F a‖≤CF) :
    multiplyCLM (family_coefficient_memLp T hBm hB) (source hR T hFm hF)=
      source hR T (hBm.mul hFm) (family_product_bound T hCB hB hF) := by
  apply Lp.ext
  have hk : ∀ᵐz∂reference R T,z.2∈cube R:=
    Measure.quasiMeasurePreserving_snd.ae (ReferenceFrequencySpace.reference_support R)
  filter_upwards [multiply_ae (family_coefficient_memLp T hBm hB) (source hR T hFm hF),
    source_ae hR T hFm hF,source_ae hR T (hBm.mul hFm) (family_product_bound T hCB hB hF),hk]
    with z hm hf hprod hz
  change multiply (family_coefficient_memLp T hBm hB) (source hR T hFm hF) z=_
  erw [hm,hf,hprod]
  rw [show field F z=F z.1 ⟨z.2,hz⟩ from field_on_cube F z.1 ⟨z.2,hz⟩,
    show field B z=B z.1 ⟨z.2,hz⟩ from field_on_cube B z.1 ⟨z.2,hz⟩,
    show field (fun a=>B a*F a) z=(B z.1*F z.1) ⟨z.2,hz⟩ from
      field_on_cube (fun a=>B a*F a) z.1 ⟨z.2,hz⟩,ContinuousMap.mul_apply,mul_comm]

set_option backward.isDefEq.respectTransparency false in
theorem product_source_slice_ae {R : ℝ} (hR : 0<R) (T : ℝ)
    {B F : Base→C(cube R,ℝ)} {CB CF : ℝ} (hCB : 0≤CB)
    (hBm : Measurable B) (hFm : Measurable F)
    (hB : ∀ᵐa∂baseMeasure T,‖B a‖≤CB) (hF : ∀ᵐa∂baseMeasure T,‖F a‖≤CF) :
    ∀ᵐa∂baseMeasure T,
      slice (multiplyCLM (family_coefficient_memLp T hBm hB) (source hR.le T hFm hF)) a=
        ContinuousSourceCoordinates.sourceMap hR (B a*F a) := by
  erw [source_product hR.le T hCB hBm hFm hB hF]
  exact source_slice_ae hR T (hBm.mul hFm) (family_product_bound T hCB hB hF)

end
end Resonance.SpacetimeSourceProducts
