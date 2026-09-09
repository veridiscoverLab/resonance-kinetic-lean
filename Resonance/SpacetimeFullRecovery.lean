import Resonance.SpacetimeDifferenceSlices
import Resonance.ProductL2MultiplierSlices
import Resonance.ActualFullRecovery

/-! Integrate the original five-Gram recovery on the same common base.
The displayed slice constraints are the original five moments of the same
global multiplied source; they are not a Hilbert orthogonal projection. -/
open Set MeasureTheory MeasureTheory.Measure
open scoped ENNReal
namespace Resonance.SpacetimeFullRecovery
noncomputable section
open ResonantMeasure Thermodynamics SpacetimePairing SpacetimeReference
open SpacetimeDifference SpacetimeDifferenceSlices ProductL2Slices
open ProductL2MultiplierSlices LpOperators PhysicalFiveBasis

theorem norm_square_lintegral_slices {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    {μ : Measure A} {ν : Measure B} [SFinite μ] [SFinite ν]
    (u : Lp ℝ 2 (μ.prod ν)) :
    ENNReal.ofReal (‖u‖^2)=∫⁻a,ENNReal.ofReal (‖slice u a‖^2)∂μ := by
  rw [ProductL2Slices.norm_square_integral]
  exact ofReal_integral_eq_lintegral_ofReal (slice_square_integrable u)
    (ae_of_all _ (fun a=>sq_nonneg _))

theorem sliceEnergy_nonnegative {R : ℝ} (hR : 0≤R) (T : ℝ)
    (θ : Base→Parameter) (u : Space R T) (a : Base) : 0 ≤ sliceEnergy hR T θ u a := by
  unfold sliceEnergy
  split_ifs
  · exact sq_nonneg _
  · exact le_rfl

set_option backward.isDefEq.respectTransparency false in
theorem full_recovery {R m M : ℝ} (hR : 0 < R) (hm0 : 0 < m) (hM : 0 ≤ M)
    {K : Set Parameter} (hK : IsCompact K) (hpos : K⊆positiveDomain R) :
    ∃C:ℝ,0<C ∧ ∀T:ℝ,∀θ:Base→Parameter,∀hm:Measurable θ,
      ∀hθ:(∀ᵐa∂baseMeasure T,θ a∈K),∀b:Source→ℝ,
      ∀hb:MemLp b ∞ (reference R T),
      (∀ᵐz∂reference R T,m ≤ b z ∧ b z ≤ M)→∀y u:Space R T,
      (∀ᵐa∂baseMeasure T,∀ha:θ a∈positiveDomain R,
        analysisMap hR ha (slice (multiplyCLM hb y) a)=0 ∧ analysisMap hR ha (slice u a)=0)→
      ‖y-u‖^2≤C*(‖physicalDifference hR T hK hpos hm hθ (y-u)‖^2+
        ‖(multiplyCLM hb-1) u‖^2) := by
  obtain ⟨C,hC,hrec⟩:=ActualFullRecovery.original_full_recovery_bound hR hm0 hM hK hpos
  refine ⟨C,hC,?_⟩
  intro T θ hm hθ b hb hbnd y u hmatch
  letI:=SpacetimeReference.reference_finite hR.le
  let e:Space R T:=(multiplyCLM hb-1) u
  have hpoint : ∀ᵐa∂baseMeasure T,
      ‖slice (y-u) a‖^2≤C*(sliceEnergy hR.le T θ (y-u) a+‖slice e a‖^2) := by
    filter_upwards [hθ,hmatch,coefficient_memLp_ae hb,ae_ae_of_ae_prod hbnd,
      multiply_slice_ae hb y,sub_identity_slice_ae hb u,slice_sub_ae y u]
      with a ha hmatch hmem hbounds hmul herr hsub
    have hap:=hpos ha
    have hbvol:=((ReferenceFrequencySpace.reference_volume_equivalent hR).1).ae_le hbounds
    have hy : analysisMap hR hap (multiplyCLM hmem (slice y a))=0 := by
      have hh:=(hmatch hap).1
      erw [hmul] at hh
      simpa only [fiberMultiplier,dif_pos hmem] using hh
    have hh:=hrec (θ a) ha (fun k=>b (a,k)) hmem hbvol (slice y a) (slice u a) hy (hmatch hap).2
    change ‖slice (y-u) a‖^2≤C*(sliceEnergy hR.le T θ (y-u) a+
      ‖slice ((multiplyCLM hb-1) u) a‖^2)
    erw [herr,hsub]
    simpa only [sliceEnergy,dif_pos hap,hsub,fiberMultiplier,dif_pos hmem] using hh
  have heq:=full_norm_disintegration hR T hK hpos hm hθ (y-u)
  have hineq : ENNReal.ofReal (‖y-u‖^2)≤
      ENNReal.ofReal C*(ENNReal.ofReal (‖physicalDifference hR T hK hpos hm hθ (y-u)‖^2)+
        ENNReal.ofReal (‖e‖^2)) := by
    rw [norm_square_lintegral_slices,heq,norm_square_lintegral_slices]
    rw [←lintegral_add_right' _ (slice_square_integrable e).aestronglyMeasurable.aemeasurable.ennreal_ofReal,
      ←lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    apply lintegral_mono_ae
    filter_upwards [hpoint] with a ha
    have hh:=ENNReal.ofReal_le_ofReal ha
    rw [ENNReal.ofReal_mul hC.le,ENNReal.ofReal_add
      (sliceEnergy_nonnegative hR.le T θ (y-u) a) (sq_nonneg _)] at hh
    exact hh
  rw [←ENNReal.ofReal_add (sq_nonneg _) (sq_nonneg _),←ENNReal.ofReal_mul hC.le] at hineq
  exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hineq

end
end Resonance.SpacetimeFullRecovery
