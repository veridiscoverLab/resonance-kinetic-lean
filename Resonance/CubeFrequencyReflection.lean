import Resonance.CollisionFrequencyConvolution

/-! Exact original cube symmetries extend the convolution identity to
all faces and all eight corners, including mixed signs. -/
open Real Set MeasureTheory
open scoped ENNReal Topology
namespace Resonance.CubeFrequencyReflection
noncomputable section
set_option maxHeartbeats 1000000
open Resonance.PlaneCoarea Resonance.CubeAxisCoordinates Resonance.CubeAxisScaling
open Resonance.FixedEnergyDensity Resonance.CollisionFrequencyConvolution
open Resonance.CornerConvolution

theorem rectangleFour_isometry (J:E≃ₗᵢ[ℝ]E) (k x y:E) :
    rectangleFour (J k) (J x) (J y)=fun l=>J (rectangleFour k x y l) := by
  ext l j
  fin_cases l <;> simp [rectangleFour,map_add]

theorem scalar_readout_isometry (R:ℝ) (J:E≃ₗᵢ[ℝ]E)
    (hJ:∀x:E,J x∈ResonantMeasure.cube R ↔ x∈ResonantMeasure.cube R)
    (k:E) (F:ℝ→ℝ≥0∞) (p:E×E) :
    scalarSharpReadout R (J k) F (J p.1,J p.2)=scalarSharpReadout R k F p := by
  classical
  have hflags : (J p.1,J p.2)∈sharpPairSet R (J k) ↔ p∈sharpPairSet R k := by
    change (∀l,rectangleFour (J k) (J p.1) (J p.2) l∈ResonantMeasure.cube R) ↔
      (∀l,rectangleFour k p.1 p.2 l∈ResonantMeasure.cube R)
    rw [rectangleFour_isometry]
    exact forall_congr' (fun l=>hJ _)
  unfold scalarSharpReadout
  by_cases hp:p∈sharpPairSet R k
  · rw [Set.indicator_of_mem hp,Set.indicator_of_mem (hflags.mpr hp),J.inner_map_map]
  · rw [Set.indicator_of_notMem hp,Set.indicator_of_notMem (fun h=>hp (hflags.mp h))]

theorem geometricFrequency_isometry {R:ℝ} (hR:0≤R) (J:E≃ₗᵢ[ℝ]E)
    (hJ:∀x:E,J x∈ResonantMeasure.cube R ↔ x∈ResonantMeasure.cube R)
    (k:E) (hk:k∈ResonantMeasure.cube R) :
    ENNReal.ofReal (CollisionFrequency.geometricFrequency R (J k))=
      ENNReal.ofReal (CollisionFrequency.geometricFrequency R k) := by
  have hd : (volume:Measure ℝ).withDensity (fiberDensity R (J k))=
      (volume:Measure ℝ).withDensity (fiberDensity R k) := by
    apply Measure.ext_of_lintegral
    intro F hF
    rw [lintegral_withDensity_eq_lintegral_mul _ (fiberDensity_measurable hR _) hF,
      lintegral_withDensity_eq_lintegral_mul _ (fiberDensity_measurable hR _) hF]
    simp only [Pi.mul_apply]
    simp_rw [mul_comm (fiberDensity _ _ _) (F _)]
    rw [sharp_energy_eq_scalar hR _ F hF,sharp_energy_eq_scalar hR _ F hF]
    have hp : MeasurePreserving (fun p:E×E=>(J p.1,J p.2)) volume volume :=
      J.measurePreserving.prod J.measurePreserving
    have he := lintegral_map (μ:=(volume:Measure (E×E)))
      (scalarSharpReadout_measurable R (J k) (fun t=>F (2*t)) (by fun_prop)) hp.measurable
    rw [hp.map_eq] at he
    rw [he]
    exact lintegral_congr (scalar_readout_isometry R J hJ k (fun t=>F (2*t)))
  have hae := (withDensity_eq_iff_of_sigmaFinite
    (fiberDensity_measurable hR (J k)).aemeasurable (fiberDensity_measurable hR k).aemeasurable).mp hd
  have he := continuousAt_zero_eq_of_ae_eq hae
    (fiberDensity_continuousAt_zero hR (J k) ((hJ k).mpr hk))
    (fiberDensity_continuousAt_zero hR k hk)
  simpa only [fiberDensity_zero] using he

def reflectionAt (k:E) : E≃ₗᵢ[ℝ]E :=
  LinearIsometryEquiv.piLpCongrRight 2 (fun i:Fin 3=>
    if k i<0 then LinearIsometryEquiv.neg ℝ else LinearIsometryEquiv.refl ℝ ℝ)

theorem reflectionAt_abs (k x:E) (i:Fin 3) : |reflectionAt k x i|=|x i| := by
  classical
  by_cases hi:k i<0 <;> simp [reflectionAt,hi]

theorem reflectionAt_cube (R:ℝ) (k x:E) :
    reflectionAt k x∈ResonantMeasure.cube R ↔ x∈ResonantMeasure.cube R := by
  change (∀i,|reflectionAt k x i|≤R) ↔ (∀i,|x i|≤R)
  simp_rw [reflectionAt_abs]

theorem reflectionAt_self (k:E) (i:Fin 3) : reflectionAt k k i=|k i| := by
  classical
  by_cases hi:k i<0
  · simp [reflectionAt,hi,abs_of_neg hi]
  · simp [reflectionAt,hi,abs_of_nonneg (le_of_not_gt hi)]

def cornerCoordinates (R:ℝ) (k:E) (i:Fin 3) : ℝ := (R-|k i|)/(2*R)

theorem cornerCoordinates_bounds {R:ℝ} (hR:0<R) (k:E) (hk:k∈ResonantMeasure.cube R)
    (i:Fin 3) : 0≤cornerCoordinates R k i ∧ cornerCoordinates R k i≤1/2 := by
  unfold cornerCoordinates
  constructor
  · exact div_nonneg (sub_nonneg.mpr (hk i)) (by positivity)
  · apply (div_le_iff₀ (by positivity : 0<2*R)).mpr
    nlinarith [abs_nonneg (k i)]

theorem reflected_output_eq_scaled {R:ℝ} (hR:0<R) (k:E) :
    reflectionAt k k=(2*R)•normalizedOutput (cornerCoordinates R k) := by
  ext i
  rw [reflectionAt_self]
  change |k i|=(2*R)*(1/2-(R-|k i|)/(2*R))
  field_simp
  ring

/-- The sharp physical frequency formula on the entire closed cube.
The parameter uses the distance to the closest signed face on every
axis, so the statement includes every direction approaching a corner. -/
theorem full_cube_frequency_eq_convolution {R:ℝ} (hR:0<R) (k:E)
    (hk:k∈ResonantMeasure.cube R) :
    ENNReal.ofReal (CollisionFrequency.geometricFrequency R k)=
      ENNReal.ofReal ((2*R)^4/2)*sumDensity (cornerCoordinates R k) 0 := by
  have hc := cornerCoordinates_bounds hR k hk
  have he := geometricFrequency_isometry hR.le (reflectionAt k) (reflectionAt_cube R k) k hk
  rw [reflected_output_eq_scaled hR] at he
  have hmain := original_frequency_eq_convolution (by positivity : 0<2*R)
    (fun i=>(hc i).1) (fun i=>lt_of_le_of_lt (hc i).2 (by norm_num))
  have hrad:(2*R)/2=R := by ring
  rw [hrad] at hmain
  exact he.symm.trans hmain

end
end Resonance.CubeFrequencyReflection
