import Resonance.PairWeightLinear

/-! Actual sphere and plane instances of the complete-weight linear map.
The only scalar row bound is proved from the original unit RJ pair rows. -/
open MeasureTheory Set
open scoped ENNReal
namespace Resonance.ActualPairWeightLinear
noncomputable section
set_option maxHeartbeats 1800000
open ResonantMeasure Thermodynamics WeightedJointMeasure CollisionFrequency
open ActualPairNormalization JointWeightComparison QuartetWeightSpace
open PairWeightLinear

theorem rawWeight_one_eq (R : ℝ) (q : FourMomenta) :
    rawWeight R 1 q=CoareaNormalization.sharpReadout R (fun _=>1) q := by
  by_cases hq : q∈CoareaNormalization.allFourFlags R
  · rw [rawWeight_inside R _ hq,CoareaNormalization.sharpReadout,Set.indicator_of_mem hq]
    rfl
  · rw [rawWeight_outside R _ hq,CoareaNormalization.sharpReadout,Set.indicator_of_notMem hq]

def incomingFactor (R : ℝ) (p : E×E) : ℝ :=
  (referenceFrequency R p.2)⁻¹*(‖p.1-p.2‖/8)

def crossFactor (R : ℝ) (p : E×E) : ℝ :=
  (referenceFrequency R p.2)⁻¹*(2*‖p.2-p.1‖)⁻¹

theorem incomingFactor_measurable (R : ℝ) : Measurable (incomingFactor R) :=
  (((CollisionMarginalDensity.lossFrequency_measurable R referenceProfile_continuous.measurable).comp
    measurable_snd).inv).mul ((measurable_fst.sub measurable_snd).norm.div_const 8)

theorem crossFactor_measurable (R : ℝ) : Measurable (crossFactor R) :=
  (((CollisionMarginalDensity.lossFrequency_measurable R referenceProfile_continuous.measurable).comp
    measurable_snd).inv).mul ((measurable_const.mul (measurable_snd.sub measurable_fst).norm).inv)

theorem incomingFactor_nonnegative (R : ℝ) (p : E×E) : 0 ≤ incomingFactor R p :=
  mul_nonneg (CrossRowWeightedBounds.inverseFrequency_nonnegative R p.2) (by positivity)

theorem crossFactor_nonnegative (R : ℝ) (p : E×E) : 0≤crossFactor R p :=
  mul_nonneg (CrossRowWeightedBounds.inverseFrequency_nonnegative R p.2) (by positivity)

def incomingKernel (R : ℝ) (W : WeightSpace R) : E→E→ℝ :=
  kernel surface R IncomingPairMarginal.incomingQuartet (incomingFactor R) W

def crossKernel (R : ℝ) (W : WeightSpace R) : E→E→ℝ :=
  kernel (CrossRowPointwise.finitePlaneMeasure R) R CrossPairCoordinates.crossQuartet (crossFactor R) W

theorem unit_weight : weight unitParameter=(fun _=>1) := by
  funext q
  simp only [weight,unit_profile,Finset.prod_const_one,ENNReal.ofReal_one]

theorem incomingKernel_one {R : ℝ} (hR : 0≤R) (k p : E) :
    incomingKernel R 1 k p=(referenceFrequency R p)⁻¹*
      (IncomingPairDensity.density R (weight unitParameter) (k,p)).toReal := by
  rw [unit_weight]
  have he := IncomingRowPointwise.density_toReal_sphereRow hR (fun _=>1) continuous_const
    (fun _ _=>zero_le_one) k p
  simp only [ENNReal.ofReal_one] at he
  rw [he]
  unfold incomingKernel kernel fiber incomingFactor IncomingRowPointwise.sphereRow IncomingRowPointwise.sphereIntegral
  simp_rw [rawWeight_one_eq]
  ring

theorem crossKernel_one {R : ℝ} (hR : 0≤R) (k p : E) :
    crossKernel R 1 k p=(referenceFrequency R p)⁻¹*
      (CrossPairDensity.density R (weight unitParameter) (k,p)).toReal := by
  rw [unit_weight]
  have he := CrossDensityContinuity.density_toReal_planeRow hR (fun _=>1) continuous_const
    (fun _ _=>zero_le_one) k p
  simp only [ENNReal.ofReal_one] at he
  rw [he]
  unfold crossKernel kernel fiber crossFactor CrossRowPointwise.planeRow
  rw [CrossRowPointwise.planeIntegral_box hR]
  simp_rw [rawWeight_one_eq]
  ring

theorem unit_kernel_bounds {R : ℝ} (hR : 0≤R) (k p : E) :
    0 ≤ incomingKernel R 1 k p ∧ incomingKernel R 1 k p≤LinftyParameterContinuity.baseRow R k p ∧
    0≤crossKernel R 1 k p ∧ crossKernel R 1 k p≤LinftyParameterContinuity.baseRow R k p := by
  rw [incomingKernel_one hR,crossKernel_one hR]
  have hi : 0≤(referenceFrequency R p)⁻¹*
      (IncomingPairDensity.density R (weight unitParameter) (k,p)).toReal :=
    mul_nonneg (CrossRowWeightedBounds.inverseFrequency_nonnegative R p) ENNReal.toReal_nonneg
  have hc : 0≤(referenceFrequency R p)⁻¹*
      (CrossPairDensity.density R (weight unitParameter) (k,p)).toReal :=
    mul_nonneg (CrossRowWeightedBounds.inverseFrequency_nonnegative R p) ENNReal.toReal_nonneg
  unfold LinftyParameterContinuity.baseRow NormalizedPairParameterBounds.baseDensity
  refine ⟨hi,?_,hc,?_⟩ <;> nlinarith

theorem unit_rows_uniform {R : ℝ} (hR : 0<R) :
    ∃B : ℝ,0≤B ∧ ∀k∈cube R,
      (Integrable (incomingKernel R 1 k) (cubeVolume R) ∧
        (∫p,incomingKernel R 1 k p∂cubeVolume R)≤B) ∧
      (Integrable (crossKernel R 1 k) (cubeVolume R) ∧
        (∫p,crossKernel R 1 k p∂cubeVolume R)≤B) := by
  obtain ⟨B,hB,hb⟩ := LinftyParameterContinuity.baseRow_uniform_bound hR
  refine ⟨B,hB,?_⟩
  intro k hk
  have him := kernel_measurable surface R _ IncomingPairMarginal.incomingQuartet_measurable
    _ (incomingFactor_measurable R) (1 : WeightSpace R)
  have hcm := kernel_measurable (CrossRowPointwise.finitePlaneMeasure R) R _
    CrossPairCoordinates.crossQuartet_measurable _ (crossFactor_measurable R) (1 : WeightSpace R)
  have hi : Integrable (incomingKernel R 1 k) (cubeVolume R) := by
    apply (hb k hk).1.mono' (him.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable
    apply ae_of_all
    intro p
    change ‖incomingKernel R 1 k p‖≤LinftyParameterContinuity.baseRow R k p
    rw [Real.norm_of_nonneg (unit_kernel_bounds hR.le k p).1]
    exact (unit_kernel_bounds hR.le k p).2.1
  have hc : Integrable (crossKernel R 1 k) (cubeVolume R) := by
    apply (hb k hk).1.mono' (hcm.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable
    apply ae_of_all
    intro p
    change ‖crossKernel R 1 k p‖≤LinftyParameterContinuity.baseRow R k p
    rw [Real.norm_of_nonneg (unit_kernel_bounds hR.le k p).2.2.1]
    exact (unit_kernel_bounds hR.le k p).2.2.2
  refine ⟨⟨hi,?_⟩,⟨hc,?_⟩⟩
  · exact (integral_mono_ae hi (hb k hk).1
      (ae_of_all _ (fun p=>(unit_kernel_bounds hR.le k p).2.1))).trans (hb k hk).2
  · exact (integral_mono_ae hc (hb k hk).1
      (ae_of_all _ (fun p=>(unit_kernel_bounds hR.le k p).2.2.2))).trans (hb k hk).2

def rowBound {R : ℝ} (hR : 0<R) : ℝ := (unit_rows_uniform hR).choose

theorem rowBound_nonnegative {R : ℝ} (hR : 0<R) : 0≤rowBound hR :=
  (unit_rows_uniform hR).choose_spec.1

theorem incoming_unit_integrable {R : ℝ} (hR : 0<R) (k : E) (hk : k∈cube R) :
    Integrable (incomingKernel R 1 k) (cubeVolume R) :=
  ((unit_rows_uniform hR).choose_spec.2 k hk).1.1

theorem incoming_unit_bound {R : ℝ} (hR : 0<R) (k : E) (hk : k∈cube R) :
    (∫p,incomingKernel R 1 k p∂cubeVolume R)≤rowBound hR :=
  ((unit_rows_uniform hR).choose_spec.2 k hk).1.2

theorem cross_unit_integrable {R : ℝ} (hR : 0<R) (k : E) (hk : k∈cube R) :
    Integrable (crossKernel R 1 k) (cubeVolume R) :=
  ((unit_rows_uniform hR).choose_spec.2 k hk).2.1

theorem cross_unit_bound {R : ℝ} (hR : 0<R) (k : E) (hk : k∈cube R) :
    (∫p,crossKernel R 1 k p∂cubeVolume R)≤rowBound hR :=
  ((unit_rows_uniform hR).choose_spec.2 k hk).2.2

def incomingOperator {R : ℝ} (hR : 0<R) :
    WeightSpace R→L[ℝ](LinftyMultiplication.X R→L[ℝ]LinftyMultiplication.X R) :=
  weightOperator surface R _ IncomingPairMarginal.incomingQuartet_measurable _
    (incomingFactor_measurable R) (incomingFactor_nonnegative R)
    (incoming_unit_integrable hR) (rowBound hR) (rowBound_nonnegative hR) (incoming_unit_bound hR)

def crossOperator {R : ℝ} (hR : 0<R) :
    WeightSpace R→L[ℝ](LinftyMultiplication.X R→L[ℝ]LinftyMultiplication.X R) :=
  weightOperator (CrossRowPointwise.finitePlaneMeasure R) R _ CrossPairCoordinates.crossQuartet_measurable _
    (crossFactor_measurable R) (crossFactor_nonnegative R)
    (cross_unit_integrable hR) (rowBound hR) (rowBound_nonnegative hR) (cross_unit_bound hR)

theorem incomingOperator_ae {R : ℝ} (hR : 0<R) (W : WeightSpace R) (f : LinftyMultiplication.X R) :
    incomingOperator hR W f=ᵐ[cubeVolume R] fun k=>∫p,incomingKernel R W k p*f p∂cubeVolume R :=
  inputOperator_ae surface R _ IncomingPairMarginal.incomingQuartet_measurable _
    (incomingFactor_measurable R) (incomingFactor_nonnegative R)
    (incoming_unit_integrable hR) (rowBound hR) (rowBound_nonnegative hR) (incoming_unit_bound hR) W f

theorem crossOperator_ae {R : ℝ} (hR : 0<R) (W : WeightSpace R) (f : LinftyMultiplication.X R) :
    crossOperator hR W f=ᵐ[cubeVolume R] fun k=>∫p,crossKernel R W k p*f p∂cubeVolume R :=
  inputOperator_ae (CrossRowPointwise.finitePlaneMeasure R) R _ CrossPairCoordinates.crossQuartet_measurable _
    (crossFactor_measurable R) (crossFactor_nonnegative R)
    (cross_unit_integrable hR) (rowBound hR) (rowBound_nonnegative hR) (cross_unit_bound hR) W f

theorem incomingOperator_norm_le {R : ℝ} (hR : 0<R) : ‖incomingOperator hR‖≤rowBound hR :=
  weightOperator_norm_le surface R _ IncomingPairMarginal.incomingQuartet_measurable _
    (incomingFactor_measurable R) (incomingFactor_nonnegative R)
    (incoming_unit_integrable hR) (rowBound hR) (rowBound_nonnegative hR) (incoming_unit_bound hR)

theorem crossOperator_norm_le {R : ℝ} (hR : 0<R) : ‖crossOperator hR‖≤rowBound hR :=
  weightOperator_norm_le (CrossRowPointwise.finitePlaneMeasure R) R _ CrossPairCoordinates.crossQuartet_measurable _
    (crossFactor_measurable R) (crossFactor_nonnegative R)
    (cross_unit_integrable hR) (rowBound hR) (rowBound_nonnegative hR) (cross_unit_bound hR)

end
end Resonance.ActualPairWeightLinear
