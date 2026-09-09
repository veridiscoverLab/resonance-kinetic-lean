import Resonance.ContinuousRowOperator
import Resonance.CrossReferenceRowL1
import Resonance.IncomingRowL1

/-! The original two pair densities, divided by the original reference
loss frequency in their input variable, define compact operators on the
real continuous functions on the full closed physical cube. -/
open MeasureTheory Set Filter
open scoped ENNReal Topology
namespace Resonance.ActualReferenceRowOperator
noncomputable section
set_option maxHeartbeats 900000
open ResonantMeasure CollisionFrequency CrossRowWeightedBounds

def cubeMeasure (R : ℝ) : Measure (cube R) :=
  Measure.comap Subtype.val (volume : Measure E)

def crossRow (R : ℝ) (θ : Thermodynamics.Parameter) (k p : cube R) : ℝ :=
  (referenceFrequency R p)⁻¹ *
    (CrossPairDensity.density R (WeightedJointMeasure.weight θ) (k,p)).toReal

def incomingRow (R : ℝ) (θ : Thermodynamics.Parameter) (k p : cube R) : ℝ :=
  (referenceFrequency R p)⁻¹ *
    (IncomingPairDensity.density R (WeightedJointMeasure.weight θ) (k,p)).toReal

theorem crossRow_integrable {R : ℝ} (hR : 0 < R)
    {θ : Thermodynamics.Parameter} (hθ : θ ∈ Thermodynamics.positiveDomain R)
    (k : cube R) : Integrable (crossRow R θ k) (cubeMeasure R) := by
  obtain ⟨Φ,hΦ,hpos,he⟩ := CrossDensityContinuity.actual_weight_extension hθ
  have hrow (p : E) :
      (CrossPairDensity.density R (WeightedJointMeasure.weight θ) ((k:E),p)).toReal =
        CrossRowPointwise.planeRow R Φ k p := by
    rw [CrossDensityContinuity.density_congr_on_flags R _ _ he,
      CrossDensityContinuity.density_toReal_planeRow hR.le Φ hΦ hpos]
  have hi := weighted_planeRow_integrable hR Φ hΦ hpos k
  have hi' := (integrableOn_iff_comap_subtypeVal
    (FiberContinuity.cube_isClosed R).measurableSet).mp hi
  change Integrable (fun p : cube R => (referenceFrequency R p)⁻¹ *
    (CrossPairDensity.density R (WeightedJointMeasure.weight θ) ((k:E),(p:E))).toReal)
    (Measure.comap Subtype.val volume)
  simp_rw [hrow]
  exact hi'

theorem incomingRow_integrable {R : ℝ} (hR : 0 < R)
    {θ : Thermodynamics.Parameter} (hθ : θ ∈ Thermodynamics.positiveDomain R)
    (k : cube R) : Integrable (incomingRow R θ k) (cubeMeasure R) := by
  obtain ⟨Φ,hΦ,hpos,he⟩ := CrossDensityContinuity.actual_weight_extension hθ
  have hrow (p : E) :
      (IncomingPairDensity.density R (WeightedJointMeasure.weight θ) ((k:E),p)).toReal =
        IncomingRowPointwise.sphereRow R Φ k p := by
    rw [IncomingRowPointwise.density_congr_on_flags R _ _ he,
      IncomingRowPointwise.density_toReal_sphereRow hR.le Φ hΦ hpos]
  obtain ⟨B,hB,hbound⟩ := IncomingRowL1.sphereRow_uniform_bound hR.le Φ hΦ
  have hi : Integrable (fun p : E => (referenceFrequency R p)⁻¹ *
      IncomingRowPointwise.sphereRow R Φ k p) (volume.restrict (cube R)) :=
    (CornerInverseFrequency.reference_inverse_integrable hR).mul_bdd
      (IncomingRowL1.sphereRow_measurable hR.le Φ hΦ hpos k).aestronglyMeasurable
      (by filter_upwards [ae_restrict_mem (FiberContinuity.cube_isClosed R).measurableSet]
            with p hp
          exact hbound k k.property p hp)
  have hi' := (integrableOn_iff_comap_subtypeVal
    (FiberContinuity.cube_isClosed R).measurableSet).mp hi
  change Integrable (fun p : cube R => (referenceFrequency R p)⁻¹ *
    (IncomingPairDensity.density R (WeightedJointMeasure.weight θ) ((k:E),(p:E))).toReal)
    (Measure.comap Subtype.val volume)
  simp_rw [hrow]
  exact hi'

theorem crossRow_L1_continuous {R : ℝ} (hR : 0 < R)
    {θ : Thermodynamics.Parameter} (hθ : θ ∈ Thermodynamics.positiveDomain R)
    (k : cube R) :
    Tendsto (fun a : cube R => ∫ p, ‖crossRow R θ a p-crossRow R θ k p‖ ∂cubeMeasure R)
      (𝓝 k) (𝓝 0) := by
  have ht := (tendsto_nhdsWithin_iff_subtype k.property _ _).mp
    (CrossReferenceRowL1.actual_cross_reference_weighted_L1 hR hθ k.property)
  have heq (a : cube R) : (∫ p, ‖crossRow R θ a p-crossRow R θ k p‖ ∂cubeMeasure R) =
      ∫ p in cube R, (referenceFrequency R p)⁻¹ *
        ‖(CrossPairDensity.density R (WeightedJointMeasure.weight θ) ((a:E),p)).toReal-
          (CrossPairDensity.density R (WeightedJointMeasure.weight θ) ((k:E),p)).toReal‖ := by
    unfold crossRow cubeMeasure
    rw [integral_subtype_comap (FiberContinuity.cube_isClosed R).measurableSet
      (fun p : E => ‖(referenceFrequency R p)⁻¹ *
        (CrossPairDensity.density R (WeightedJointMeasure.weight θ) ((a:E),p)).toReal-
        (referenceFrequency R p)⁻¹ *
        (CrossPairDensity.density R (WeightedJointMeasure.weight θ) ((k:E),p)).toReal‖)]
    apply integral_congr_ae
    filter_upwards [] with p
    rw [← mul_sub,norm_mul,Real.norm_of_nonneg
      (show 0 ≤ (referenceFrequency R p)⁻¹ from inverseFrequency_nonnegative R p)]
  simpa only [heq,Set.restrict_apply] using ht

theorem incomingRow_L1_continuous {R : ℝ} (hR : 0 < R)
    {θ : Thermodynamics.Parameter} (hθ : θ ∈ Thermodynamics.positiveDomain R)
    (k : cube R) :
    Tendsto (fun a : cube R => ∫ p, ‖incomingRow R θ a p-incomingRow R θ k p‖ ∂cubeMeasure R)
      (𝓝 k) (𝓝 0) := by
  have ht := (tendsto_nhdsWithin_iff_subtype k.property _ _).mp
    (IncomingRowL1.actual_incoming_reference_weighted_L1 hR hθ k.property)
  have heq (a : cube R) : (∫ p, ‖incomingRow R θ a p-incomingRow R θ k p‖ ∂cubeMeasure R) =
      ∫ p in cube R, (referenceFrequency R p)⁻¹ *
        ‖(IncomingPairDensity.density R (WeightedJointMeasure.weight θ) ((a:E),p)).toReal-
          (IncomingPairDensity.density R (WeightedJointMeasure.weight θ) ((k:E),p)).toReal‖ := by
    unfold incomingRow cubeMeasure
    rw [integral_subtype_comap (FiberContinuity.cube_isClosed R).measurableSet
      (fun p : E => ‖(referenceFrequency R p)⁻¹ *
        (IncomingPairDensity.density R (WeightedJointMeasure.weight θ) ((a:E),p)).toReal-
        (referenceFrequency R p)⁻¹ *
        (IncomingPairDensity.density R (WeightedJointMeasure.weight θ) ((k:E),p)).toReal‖)]
    apply integral_congr_ae
    filter_upwards [] with p
    rw [← mul_sub,norm_mul,Real.norm_of_nonneg
      (show 0 ≤ (referenceFrequency R p)⁻¹ from inverseFrequency_nonnegative R p)]
  simpa only [heq,Set.restrict_apply] using ht

theorem actual_cross_compact {R : ℝ} (hR : 0 < R)
    {θ : Thermodynamics.Parameter} (hθ : θ ∈ Thermodynamics.positiveDomain R) :
    ∃ T : C(cube R,ℝ) →L[ℝ] C(cube R,ℝ), IsCompactOperator T ∧
      ∀ f k, T f k = ∫ p, crossRow R θ k p*f p ∂cubeMeasure R :=
  ContinuousRowOperator.exists_compact_operator (crossRow R θ)
    (crossRow_integrable hR hθ) (crossRow_L1_continuous hR hθ)

theorem actual_incoming_compact {R : ℝ} (hR : 0 < R)
    {θ : Thermodynamics.Parameter} (hθ : θ ∈ Thermodynamics.positiveDomain R) :
    ∃ T : C(cube R,ℝ) →L[ℝ] C(cube R,ℝ), IsCompactOperator T ∧
      ∀ f k, T f k = ∫ p, incomingRow R θ k p*f p ∂cubeMeasure R :=
  ContinuousRowOperator.exists_compact_operator (incomingRow R θ)
    (incomingRow_integrable hR hθ) (incomingRow_L1_continuous hR hθ)

end
end Resonance.ActualReferenceRowOperator
