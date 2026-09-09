import Resonance.CrossRowL1
import Resonance.CornerNewtonRows
import Resonance.MarginalInverseBounds

/-! The singular input weight is the actual reference loss frequency.
Full-row integrability and uniform corner tails are established before
using real-valued integrals. -/
open MeasureTheory Set Real Filter
open scoped ENNReal Topology
namespace Resonance.CrossRowWeightedBounds
noncomputable section
set_option maxHeartbeats 900000
open ResonantMeasure CrossRowPointwise CrossDensityContinuity CrossRowMass
open CollisionFrequency CornerInverseFrequency CornerNewtonTail NewtonPotentialTails

def inverseFrequency (R : ℝ) (p : E) : ℝ := (referenceFrequency R p)⁻¹

theorem referenceFrequency_nonnegative (R : ℝ) (p : E) : 0 ≤ referenceFrequency R p := by
  unfold referenceFrequency lossFrequency FiberContinuity.fiberReadout
  apply mul_nonneg (inv_nonneg.mpr (referenceProfile_positive p).le)
  apply integral_nonneg
  intro q
  exact mul_nonneg (mul_nonneg (referenceProfile_positive _).le
    (referenceProfile_positive _).le) (referenceProfile_positive _).le

theorem inverseFrequency_nonnegative (R : ℝ) (p : E) : 0 ≤ inverseFrequency R p :=
  inv_nonneg.mpr (referenceFrequency_nonnegative R p)

theorem planeRow_kernel_bound {R : ℝ} (hR : 0 ≤ R)
    (Φ : FourMomenta → ℝ) (hΦ : Continuous Φ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ k p : E,
      ENNReal.ofReal (planeRow R Φ k p) ≤ ENNReal.ofReal C*(1+kernelOne (k-p)) := by
  obtain ⟨B,hB,hbound⟩ := PolarCoordinates.continuous_four_flags_bound hR Φ hΦ
  let C : ℝ := B*(finitePlaneMeasure R).real univ/2
  have hC : 0 ≤ C := by dsimp [C]; positivity
  refine ⟨C,hC,?_⟩
  intro k p
  have hi : ‖planeIntegral R Φ k p‖ ≤ B*(finitePlaneMeasure R).real univ := by
    rw [planeIntegral_box hR]
    exact norm_integral_le_of_norm_le_const (ae_of_all _ (crossSharp_bound hB Φ hbound k p))
  have hb : planeRow R Φ k p ≤ C*‖k-p‖⁻¹ := by
    apply (le_abs_self _).trans
    rw [← Real.norm_eq_abs,planeRow,norm_mul,
      Real.norm_of_nonneg (inv_nonneg.mpr (by positivity))]
    apply (mul_le_mul_of_nonneg_left hi (inv_nonneg.mpr (by positivity))).trans_eq
    dsimp [C]
    rw [mul_inv,norm_sub_rev k p]
    ring
  calc
    _ ≤ ENNReal.ofReal (C*‖k-p‖⁻¹) := ENNReal.ofReal_le_ofReal hb
    _ = ENNReal.ofReal C*kernelOne (k-p) := by rw [ENNReal.ofReal_mul hC]; rfl
    _ ≤ _ := mul_le_mul_right (le_add_self : kernelOne (k-p) ≤ 1+kernelOne (k-p)) _

theorem weighted_planeRow_lintegral_bound {R C : ℝ} (_hC : 0 ≤ C)
    {Φ : FourMomenta → ℝ}
    (hbound : ∀ k p : E, ENNReal.ofReal (planeRow R Φ k p) ≤ ENNReal.ofReal C*(1+kernelOne (k-p)))
    (k : E) (T : Set E) :
    (∫⁻ p in T, ENNReal.ofReal (inverseFrequency R p*planeRow R Φ k p)) ≤
      ENNReal.ofReal C*(∫⁻ p in T, ENNReal.ofReal ((referenceFrequency R p)⁻¹)*(1+kernelOne (k-p))) := by
  have hm : Measurable (fun p : E => ENNReal.ofReal ((referenceFrequency R p)⁻¹)*(1+kernelOne (k-p))) := by
    exact (MarginalInverseBounds.referenceInverse_measurable R).mul
      (measurable_const.add (kernelOne_measurable.comp (measurable_const.sub measurable_id)))
  rw [← lintegral_const_mul _ hm]
  apply lintegral_mono
  intro p
  dsimp only
  rw [ENNReal.ofReal_mul (inverseFrequency_nonnegative R p)]
  calc
    _ ≤ ENNReal.ofReal (inverseFrequency R p) *
        (ENNReal.ofReal C*(1+kernelOne (k-p))) := by gcongr; exact hbound k p
    _ = _ := by dsimp [inverseFrequency]; ring

theorem weighted_planeRow_integrable {R : ℝ} (hR : 0 < R)
    (Φ : FourMomenta → ℝ) (hΦ : Continuous Φ)
    (hpos : ∀ q ∈ CoareaNormalization.allFourFlags R, 0 ≤ Φ q) (k : E) :
    Integrable (fun p => inverseFrequency R p*planeRow R Φ k p) (volume.restrict (cube R)) := by
  obtain ⟨C,hC,hbound⟩ := planeRow_kernel_bound hR.le Φ hΦ
  obtain ⟨K,hK,hrow⟩ := CornerNewtonRows.reference_newton_row_bound hR
  apply (lintegral_ofReal_ne_top_iff_integrable
    ((reference_inverse_integrable hR).aestronglyMeasurable.mul
      (planeRow_measurable hR.le Φ hΦ hpos k).aestronglyMeasurable)
    (ae_of_all _ (fun p => mul_nonneg (inverseFrequency_nonnegative R p) (planeRow_nonnegative hpos k p)))).mp
  apply ne_of_lt
  apply lt_of_le_of_lt (weighted_planeRow_lintegral_bound hC hbound k (cube R))
  apply lt_of_le_of_lt (mul_le_mul_right (hrow k) _)
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top

theorem weighted_planeRow_tail {R : ℝ} (hR : 0 < R)
    (Φ : FourMomenta → ℝ) (hΦ : Continuous Φ)
    (hpos : ∀ q ∈ CoareaNormalization.allFourFlags R, 0 ≤ Φ q) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ η : ℝ, 0 < η → η ≤ Real.exp (-8) → ∀ k : E,
      (∫ p in fullTail R η, inverseFrequency R p*planeRow R Φ k p) ≤ K/Real.log (1/η) := by
  obtain ⟨C,hC,hbound⟩ := planeRow_kernel_bound hR.le Φ hΦ
  obtain ⟨K,hK,hrow⟩ := reference_newton_tail hR
  refine ⟨C*K,mul_nonneg hC hK,?_⟩
  intro η hη hηsmall k
  have hlog : 0 < Real.log (1/η) := by
    have hh := Real.log_le_log hη hηsmall
    rw [Real.log_exp] at hh
    rw [one_div,Real.log_inv]
    linarith
  have hi : Integrable (fun p => inverseFrequency R p*planeRow R Φ k p)
      (volume.restrict (fullTail R η)) :=
    (weighted_planeRow_integrable hR Φ hΦ hpos k).mono_measure
      (Measure.restrict_mono (fun p hp => hp.1) le_rfl)
  have hb := (weighted_planeRow_lintegral_bound hC hbound k (fullTail R η)).trans
    (mul_le_mul_right (hrow η hη hηsmall k) (ENNReal.ofReal C))
  rw [← ofReal_integral_eq_lintegral_ofReal hi
    (ae_of_all _ (fun p => mul_nonneg (inverseFrequency_nonnegative R p) (planeRow_nonnegative hpos k p))),
    ← ENNReal.ofReal_mul hC] at hb
  have he : C*(K/Real.log (1/η)) = C*K/Real.log (1/η) := by ring
  rw [he] at hb
  exact (ENNReal.ofReal_le_ofReal_iff (by positivity : 0 ≤ C*K/Real.log (1/η))).mp hb

end
end Resonance.CrossRowWeightedBounds
