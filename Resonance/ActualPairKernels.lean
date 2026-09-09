import Resonance.ActualPairNormalization

/-! The two exact pair kernels of the original full Gram operator,
normalized against the same actual frequency-weighted marginal. -/
open MeasureTheory Set
open scoped ENNReal
namespace Resonance.ActualPairKernels
noncomputable section
open ResonantMeasure WeightedJointMeasure FrequencyWeightedForm ActualPairNormalization

theorem restricted_pair_density (R : ℝ) {r : E×E→ℝ≥0∞}
    (hz : ∀p,p∉cube R×ˢcube R → r p=0) :
    ((cubeVolume R).prod (cubeVolume R)).withDensity r=
      ((volume : Measure E).prod volume).withDensity r := by
  rw [cubeVolume,Measure.prod_restrict,←withDensity_indicator ((measurable_cube R).prod
    (measurable_cube R))]
  apply withDensity_congr_ae
  apply ae_of_all
  intro p
  by_cases hp : p∈cube R×ˢcube R
  · exact Set.indicator_of_mem hp r
  · rw [Set.indicator_of_notMem hp,hz p hp]

theorem joint_weight_bounded {R : ℝ} {θ : Thermodynamics.Parameter}
    (hθ : θ∈Thermodynamics.positiveDomain R) :
    ∃B : ℝ≥0∞,B≠∞ ∧ ∀q∈CoareaNormalization.allFourFlags R,weight θ q≤B := by
  obtain ⟨M,hM,hb⟩ := profile_bounded hθ
  refine ⟨ENNReal.ofReal (M^4),ENNReal.ofReal_ne_top,?_⟩
  intro q hq
  apply ENNReal.ofReal_le_ofReal
  calc
    (∏i : Fin 4,profile θ (q i)) ≤ ∏_i : Fin 4,M :=
      Finset.prod_le_prod (fun i _=>(profile_pos hθ (hq i)).le)
        (fun i _=>(le_abs_self _).trans (hb _ (hq i)))
    _ = M^4 := by simp

theorem incoming_density_finite {R : ℝ} {θ : Thermodynamics.Parameter}
    (hθ : θ∈Thermodynamics.positiveDomain R) (p : E×E) :
    IncomingPairDensity.density R (weight θ) p≠∞ := by
  obtain ⟨B,hB,hb⟩ := joint_weight_bounded hθ
  apply ne_of_lt
  apply lt_of_le_of_lt (IncomingPairDensity.density_bound R hb p)
  exact ENNReal.mul_lt_top (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hB.lt_top)
    (measure_lt_top surface univ)

theorem cross_density_finite {R : ℝ} (hR : 0≤R) {θ : Thermodynamics.Parameter}
    (hθ : θ∈Thermodynamics.positiveDomain R) (p : E×E) :
    CrossPairDensity.density R (weight θ) p≠∞ := by
  obtain ⟨B,hB,hb⟩ := joint_weight_bounded hθ
  apply ne_of_lt
  apply lt_of_le_of_lt (CrossPairDensity.density_bound hR hb p)
  exact ENNReal.mul_lt_top (ENNReal.mul_lt_top
    (ENNReal.mul_lt_top (by norm_num) ENNReal.ofReal_lt_top) hB.lt_top)
    (isCompact_closedBall (0 : PlaneCoarea.E2) (6*R)).measure_lt_top

def kernel01 (R : ℝ) (θ : Thermodynamics.Parameter) : E×E→ℝ :=
  NormalizedPairDensity.realKernel (marginalDensity R θ) (marginalDensity R θ)
    (IncomingPairDensity.density R (weight θ))
def kernel02 (R : ℝ) (θ : Thermodynamics.Parameter) : E×E→ℝ :=
  NormalizedPairDensity.realKernel (marginalDensity R θ) (marginalDensity R θ)
    (CrossPairDensity.density R (weight θ))

theorem normalized_actual_density {R : ℝ} (hR : 0<R) {θ : Thermodynamics.Parameter}
    (hθ : θ∈Thermodynamics.positiveDomain R) {r : E×E→ℝ≥0∞}
    (hr : Measurable r) (hrf : ∀p,r p≠∞) (hrz : ∀p,p∉cube R×ˢcube R → r p=0) :
    ((marginal R θ).prod (marginal R θ)).withDensity
      (fun p=>ENNReal.ofReal (NormalizedPairDensity.realKernel
        (marginalDensity R θ) (marginalDensity R θ) r p))=
      ((volume : Measure E).prod volume).withDensity r := by
  letI := cubeVolume_finite R
  rw [marginal_cube_density hR.le θ]
  exact (NormalizedPairDensity.normalized_real_measure (cubeVolume R) (cubeVolume R)
    (marginalDensity_measurable R θ) (marginalDensity_measurable R θ) hr
    (marginalDensity_valid_ae hR hθ) (marginalDensity_valid_ae hR hθ)
    (ae_of_all _ hrf)).trans (restricted_pair_density R hrz)

theorem incoming_pair_normalized {R : ℝ} (hR : 0<R) {θ : Thermodynamics.Parameter}
    (hθ : θ∈Thermodynamics.positiveDomain R) :
    (jointMeasure R θ).map (fun q=>(q 0,q 1))=
      ((marginal R θ).prod (marginal R θ)).withDensity (fun p=>ENNReal.ofReal (kernel01 R θ p)) := by
  rw [jointMeasure,IncomingPairDensity.weighted_pair_marginal R (weight_measurable θ)]
  exact (normalized_actual_density hR hθ
    (IncomingPairDensity.density_measurable R (weight_measurable θ))
    (incoming_density_finite hθ) (fun p hp=>IncomingPairDensity.density_zero_outside R _ hp)).symm

theorem cross_pair_normalized {R : ℝ} (hR : 0<R) {θ : Thermodynamics.Parameter}
    (hθ : θ∈Thermodynamics.positiveDomain R) :
    (jointMeasure R θ).map (fun q=>(q 0,q 2))=
      ((marginal R θ).prod (marginal R θ)).withDensity (fun p=>ENNReal.ofReal (kernel02 R θ p)) := by
  rw [jointMeasure,CrossPairDensity.weighted_pair_marginal hR.le (weight_measurable θ)]
  exact (normalized_actual_density hR hθ
    (CrossPairDensity.density_measurable R (weight_measurable θ))
    (cross_density_finite hR.le hθ) (fun p hp=>CrossPairDensity.density_zero_outside R _ hp)).symm

end
end Resonance.ActualPairKernels
