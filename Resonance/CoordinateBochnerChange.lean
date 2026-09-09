import Resonance.CoordinateReplacement
import Resonance.ChartedCompactSupport

/-! Signed and Banach-valued coordinate change, with the accompanying genuine
integrability equivalence. The determinant is the actual scalar partial. -/
open Set MeasureTheory
namespace Resonance.CoordinateBochnerChange
noncomputable section
open PinnedMeasure CoordinateReplacement
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem inverse_integral (i : Fin 3) {F : Ambient → ℝ}
    (e : OpenPartialHomeomorph Ambient Ambient) (he : (e : Ambient → Ambient)=replace i F)
    (hF : ∀p∈e.source,DifferentiableAt ℝ F p)
    (hn : ∀p∈e.source,(fderiv ℝ F p) (CoordinateReplacement.unit i)≠0)
    (B : Ambient → E) :
    ∫p in e.source,B p = ∫q in e.target,
      |(fderiv ℝ F (e.symm q)) (CoordinateReplacement.unit i)|⁻¹ • B (e.symm q) := by
  rw [integral_target_eq_integral_abs_det_fderiv_smul volume
    (fun p hp => he ▸ replace_hasFDerivAt (hF p hp).hasFDerivAt i)]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem e.open_source.measurableSet] with p hp
  change B p = |(replaceDerivative i (fderiv ℝ F p)).toLinearMap.det| •
    |(fderiv ℝ F (e.symm (e p))) (CoordinateReplacement.unit i)|⁻¹ • B (e.symm (e p))
  rw [replaceDerivative_det,e.left_inv hp,smul_smul,
    mul_inv_cancel₀ (abs_ne_zero.mpr (hn p hp)),one_smul]

theorem inverse_integrable_iff (i : Fin 3) {F : Ambient → ℝ}
    (e : OpenPartialHomeomorph Ambient Ambient) (he : (e : Ambient → Ambient)=replace i F)
    (hF : ∀p∈e.source,DifferentiableAt ℝ F p)
    (hn : ∀p∈e.source,(fderiv ℝ F p) (CoordinateReplacement.unit i)≠0)
    (B : Ambient → E) :
    IntegrableOn (fun q=>|(fderiv ℝ F (e.symm q)) (CoordinateReplacement.unit i)|⁻¹ •
      B (e.symm q)) e.target ↔ IntegrableOn B e.source := by
  have h := integrableOn_image_iff_integrableOn_abs_det_fderiv_smul volume
    e.open_source.measurableSet
    (fun p hp => (he ▸ replace_hasFDerivAt (hF p hp).hasFDerivAt i).hasFDerivWithinAt)
    e.injOn (fun q=>|(fderiv ℝ F (e.symm q)) (CoordinateReplacement.unit i)|⁻¹ •
      B (e.symm q))
  rw [e.image_source_eq_target] at h
  refine h.trans (integrable_congr ?_)
  filter_upwards [ae_restrict_mem e.open_source.measurableSet] with p hp
  change |(replaceDerivative i (fderiv ℝ F p)).toLinearMap.det| •
    |(fderiv ℝ F (e.symm (e p))) (CoordinateReplacement.unit i)|⁻¹ • B (e.symm (e p))=B p
  rw [replaceDerivative_det,e.left_inv hp,smul_smul,
    mul_inv_cancel₀ (abs_ne_zero.mpr (hn p hp)),one_smul]

end
end Resonance.CoordinateBochnerChange
