import Resonance.SpacetimeDifference
import Resonance.ContinuousSourceCoordinates
import Resonance.ProductL2Slices

/-! Jointly measurable representatives of actual continuous cube families.
The extension is used only off the original cube; every source and quartet
leg is supported on that cube. No joint measurability of a chosen Tietze
extension is assumed. -/
open Set MeasureTheory MeasureTheory.Measure
open scoped ENNReal
namespace Resonance.SpacetimeContinuousFields
noncomputable section
open ResonantMeasure SpacetimePairing SpacetimeReference

instance cubeFunctionMeasurableSpace (R : ℝ) : MeasurableSpace C(cube R,ℝ) := borel _
instance cubeFunctionBorelSpace (R : ℝ) : BorelSpace C(cube R,ℝ) := ⟨rfl⟩

def inclusion (R : ℝ) (p : Base×cube R) : Source := (p.1,(p.2:E))

theorem inclusion_injective (R : ℝ) : Function.Injective (inclusion R) := by
  rintro ⟨x,k⟩ ⟨y,l⟩ h
  have h1:=congrArg Prod.fst h
  have h2:=congrArg Prod.snd h
  exact Prod.ext h1 (Subtype.ext h2)

theorem inclusion_measurableEmbedding (R : ℝ) : MeasurableEmbedding (inclusion R) :=
  MeasurableEmbedding.id.prodMap (MeasurableEmbedding.subtype_coe (measurable_cube R))

def field {R : ℝ} (F : Base→C(cube R,ℝ)) : Source→ℝ :=
  Function.extend (inclusion R) (fun p:Base×cube R=>F p.1 p.2) (fun _=>0)

theorem field_on_cube {R : ℝ} (F : Base→C(cube R,ℝ)) (z : Base) (k : cube R) :
    field F (z,(k:E))=F z k := (inclusion_injective R).extend_apply _ _ (z,k)

theorem field_measurable {R : ℝ} {F : Base→C(cube R,ℝ)} (hF : Measurable F) :
    Measurable (field F) := by
  apply (inclusion_measurableEmbedding R).measurable_extend _ measurable_const
  exact (show Measurable (fun p:C(cube R,ℝ)×cube R=>p.1 p.2) from continuous_eval.measurable).comp
    ((hF.comp measurable_fst).prodMk measurable_snd)

theorem field_reference_bound {R : ℝ} (T : ℝ) {F : Base→C(cube R,ℝ)} {C : ℝ}
    (hF : ∀ᵐz∂baseMeasure T,‖F z‖≤C) :
    ∀ᵐz∂reference R T,‖field F z‖≤C := by
  have hbase : ∀ᵐz∂reference R T,‖F z.1‖≤C:=Measure.quasiMeasurePreserving_fst.ae hF
  have hcube : ∀ᵐz∂reference R T,z.2∈cube R:=
    Measure.quasiMeasurePreserving_snd.ae (ReferenceFrequencySpace.reference_support R)
  filter_upwards [hbase,hcube] with z hz hk
  rw [show field F z=F z.1 ⟨z.2,hk⟩ from field_on_cube F z.1 ⟨z.2,hk⟩]
  exact (F z.1).norm_coe_le_norm _ |>.trans hz

theorem field_memLp {R : ℝ} (hR : 0≤R) (T : ℝ) {F : Base→C(cube R,ℝ)} {C : ℝ}
    (hm : Measurable F) (hF : ∀ᵐz∂baseMeasure T,‖F z‖≤C) :
    MemLp (field F) 2 (reference R T) := by
  letI:=reference_finite hR
  letI : IsFiniteMeasure (reference R T):=inferInstanceAs
    (IsFiniteMeasure ((baseMeasure T).prod (ReferenceFrequencySpace.referenceMeasure R)))
  exact (memLp_top_of_bound (field_measurable hm).aestronglyMeasurable C
    (field_reference_bound T hF)).mono_exponent (by norm_num)

def source {R : ℝ} (hR : 0≤R) (T : ℝ) {F : Base→C(cube R,ℝ)} {C : ℝ}
    (hm : Measurable F) (hF : ∀ᵐz∂baseMeasure T,‖F z‖≤C) : Space R T :=
  (field_memLp hR T hm hF).toLp (field F)

theorem source_ae {R : ℝ} (hR : 0≤R) (T : ℝ) {F : Base→C(cube R,ℝ)} {C : ℝ}
    (hm : Measurable F) (hF : ∀ᵐz∂baseMeasure T,‖F z‖≤C) :
    source hR T hm hF=ᵐ[reference R T]field F := MemLp.coeFn_toLp _

set_option backward.isDefEq.respectTransparency false in
theorem source_slice_ae {R : ℝ} (hR : 0<R) (T : ℝ) {F : Base→C(cube R,ℝ)} {C : ℝ}
    (hm : Measurable F) (hF : ∀ᵐz∂baseMeasure T,‖F z‖≤C) :
    ∀ᵐa∂baseMeasure T,ProductL2Slices.slice (source hR.le T hm hF) a=
      ContinuousSourceCoordinates.sourceMap hR (F a) := by
  letI:=reference_finite hR.le
  have hprod:=ae_ae_of_ae_prod (source_ae hR.le T hm hF)
  filter_upwards [ProductL2Slices.slice_ae (source hR.le T hm hF),hprod] with a hs ha
  apply Lp.ext
  filter_upwards [hs,ha,ContinuousSourceCoordinates.sourceMap_reference_ae hR (F a),
    ReferenceFrequencySpace.reference_support R] with k hs ha hstatic hk
  erw [hs,ha,hstatic,CubeLinftyCoordinates.zeroExtension_apply R (F a) ⟨k,hk⟩]
  exact field_on_cube F a ⟨k,hk⟩

end
end Resonance.SpacetimeContinuousFields
