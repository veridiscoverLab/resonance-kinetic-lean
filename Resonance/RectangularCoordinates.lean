import Resonance.PolarCoordinates

/-! The original (k,x,y) rectangular resonance coordinates preserve actual
nine-dimensional volume. Their complete quartet and energy are retained. -/
open MeasureTheory Set Matrix
open scoped ENNReal Matrix Kronecker

namespace Resonance.RectangularCoordinates
noncomputable section
open CoareaNormalization

def block : Matrix (Fin 3) (Fin 3) ℝ := !![1, 0, 0; 1, 1, 1; 1, 1, 0]
def matrix : Matrix Index Index ℝ := block ⊗ₖ (1 : Matrix (Fin 3) (Fin 3) ℝ)
def cartesianMap : Nine →ₗ[ℝ] Nine := Matrix.toLin' matrix

theorem block_det : Matrix.det block = -1 := by
  rw [Matrix.det_fin_three]
  change (1 * 1 * 0 - 1 * 1 * 1 - 0 * 1 * 0 + 0 * 1 * 1 + 0 * 1 * 1 - 0 * 1 * 1 : ℝ) = -1
  norm_num

theorem matrix_det : Matrix.det matrix = -1 := by
  rw [matrix, Matrix.det_kronecker, block_det]
  norm_num

theorem cartesianMap_zero (z : Nine) (j : Fin 3) : cartesianMap z (0,j) = z (0,j) := by
  fin_cases j <;> simp [cartesianMap, matrix, Matrix.toLin'_apply, Matrix.mulVec,
    dotProduct, Fintype.sum_prod_type, block, Fin.sum_univ_succ, Matrix.one_apply]

theorem cartesianMap_one (z : Nine) (j : Fin 3) :
    cartesianMap z (1,j) = z (0,j) + z (1,j) + z (2,j) := by
  fin_cases j <;> simp [cartesianMap, matrix, Matrix.toLin'_apply, Matrix.mulVec,
    dotProduct, Fintype.sum_prod_type, block, Fin.sum_univ_succ, Matrix.one_apply, add_assoc]

theorem cartesianMap_two (z : Nine) (j : Fin 3) :
    cartesianMap z (2,j) = z (0,j) + z (1,j) := by
  fin_cases j <;> simp [cartesianMap, matrix, Matrix.toLin'_apply, Matrix.mulVec,
    dotProduct, Fintype.sum_prod_type, block, Fin.sum_univ_succ, Matrix.one_apply]

theorem cartesianMap_measurable : Measurable cartesianMap :=
  cartesianMap.continuous_of_finiteDimensional.measurable

theorem cartesianMap_preserves_volume : MeasurePreserving cartesianMap volume volume := by
  refine ⟨cartesianMap_measurable, ?_⟩
  have hn : Matrix.det matrix ≠ 0 := by rw [matrix_det]; norm_num
  simpa [cartesianMap, matrix_det] using Real.map_matrix_volume_pi_eq_smul_volume_pi hn

def rectangle (z : Nine) : FourMomenta :=
  ![momentumAt z 0, momentumAt z 0 + momentumAt z 1 + momentumAt z 2,
    momentumAt z 0 + momentumAt z 1, momentumAt z 0 + momentumAt z 2]

theorem rectangle_identity (z : Nine) : physicalFour (cartesianMap z) = rectangle z := by
  have h0 : momentumAt (cartesianMap z) 0 = momentumAt z 0 := by ext j; exact cartesianMap_zero z j
  have h1 : momentumAt (cartesianMap z) 1 = momentumAt z 0 + momentumAt z 1 + momentumAt z 2 := by
    ext j; exact cartesianMap_one z j
  have h2 : momentumAt (cartesianMap z) 2 = momentumAt z 0 + momentumAt z 1 := by
    ext j; exact cartesianMap_two z j
  funext i
  fin_cases i <;> simp [physicalFour, rectangle, h0, h1, h2]
  abel

theorem rectangle_energy (z : Nine) :
    energy (rectangle z) = 2 * inner ℝ (momentumAt z 1) (momentumAt z 2) := by
  change ‖momentumAt z 0‖ ^ 2 + ‖momentumAt z 0 + momentumAt z 1 + momentumAt z 2‖ ^ 2 -
    ‖momentumAt z 0 + momentumAt z 1‖ ^ 2 - ‖momentumAt z 0 + momentumAt z 2‖ ^ 2 = _
  simp only [norm_add_sq_real, inner_add_left]
  ring

theorem rectangle_integral (Φ : FourMomenta → ℝ)
    (hΦ : AEStronglyMeasurable (fun z => Φ (physicalFour z)) (volume : Measure Nine)) :
    (∫ z : Nine, Φ (physicalFour z)) = ∫ z : Nine, Φ (rectangle z) := by
  have h := integral_map cartesianMap_measurable.aemeasurable
    (cartesianMap_preserves_volume.map_eq.symm ▸ hΦ)
  rw [cartesianMap_preserves_volume.map_eq] at h
  simpa only [rectangle_identity] using h

theorem rectangle_sharp_layer_integrable {R : ℝ} (hR : 0 ≤ R) (c : ℝ)
    (Φ : FourMomenta → ℝ) (hΦ : Continuous Φ) :
    Integrable (fun z : Nine => PolarCoordinates.sharpLayer R c Φ (rectangle z)) volume := by
  have h := cartesianMap_preserves_volume.integrable_comp_of_integrable
    (PolarCoordinates.original_sharp_layer_integrable hR c Φ hΦ)
  simpa only [Function.comp_def, rectangle_identity] using h

theorem original_rectangular_sharp_layer {R : ℝ} (hR : 0 ≤ R) (c : ℝ)
    (Φ : FourMomenta → ℝ) (hΦ : Continuous Φ) :
    (∫ z : Nine, sharpReadout R Φ (physicalFour z) *
      (c * boxKernel (c * energy (physicalFour z)))) =
    ∫ z : Nine, sharpReadout R Φ (rectangle z) *
      (c * boxKernel (c * (2 * inner ℝ (momentumAt z 1) (momentumAt z 2)))) := by
  simpa only [PolarCoordinates.sharpLayer, rectangle_energy] using
    rectangle_integral (PolarCoordinates.sharpLayer R c Φ)
      (PolarCoordinates.original_sharp_layer_integrable hR c Φ hΦ).aestronglyMeasurable

end
end Resonance.RectangularCoordinates
