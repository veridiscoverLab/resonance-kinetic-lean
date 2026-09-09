import Resonance.ProfileBanachSmooth
import Resonance.CollisionMultilinear

/-! The complete fixed-output fiber parent, divided by the original reference
loss, is a bounded multilinear map into ambient cube L-infinity. Its output
need not be continuous at zero-frequency corners. -/
open MeasureTheory Set Function
open scoped ENNReal BigOperators ContDiff
namespace Resonance.NormalizedFiberMultilinear
noncomputable section
set_option maxHeartbeats 1200000
open ResonantMeasure CollisionFiber CollisionFrequency CollisionMultilinear
open ActualPairNormalization CubeLinftyCoordinates

def normalizationBound (R : ℝ) : ℝ := (1+9*R^2)^3

theorem normalizationBound_pos (R : ℝ) : 0<normalizationBound R := by
  unfold normalizationBound
  positivity

theorem parent_geometric_bound {R : ℝ} (hR : 0≤R) (legs : Fin 3→Fin 4)
    (m : Fin 3→CubeFunction R) (k : E) :
    ‖∫q,pointParent R legs q m∂fiberMeasure R k‖≤
      (∏j,‖m j‖)*geometricFrequency R k := by
  letI : IsFiniteMeasure (fiberMeasure R k) := ⟨geometricFrequency_mass_finite hR k⟩
  simpa only [geometricFrequency_eq_mass] using norm_integral_le_of_norm_le_const
    (ae_of_all (fiberMeasure R k) (fun q=>pointParent_bound R legs q m))

theorem parent_div_reference_bound {R : ℝ} (hR : 0≤R) (legs : Fin 3→Fin 4)
    (m : Fin 3→CubeFunction R) {k : E} (hk : k∈cube R) :
    ‖(∫q,pointParent R legs q m∂fiberMeasure R k)/referenceFrequency R k‖≤
      normalizationBound R*(∏j,‖m j‖) := by
  have hn := CrossRowWeightedBounds.referenceFrequency_nonnegative R k
  have hg := (referenceFrequency_geometric_bounds hR hk).1
  have hC := normalizationBound_pos R
  have hgeom : geometricFrequency R k≤normalizationBound R*referenceFrequency R k := by
    have ha : 0<1+9*R^2 := by positivity
    have hm := mul_le_mul_of_nonneg_left hg (pow_nonneg ha.le 3)
    simpa only [normalizationBound,inv_pow,←mul_assoc,mul_inv_cancel₀ (pow_ne_zero 3 ha.ne'),one_mul]
      using hm
  rw [norm_div,Real.norm_of_nonneg hn]
  by_cases hz : referenceFrequency R k=0
  · rw [hz,div_zero]
    positivity
  · have hp := lt_of_le_of_ne hn (Ne.symm hz)
    apply (div_le_iff₀ hp).mpr
    calc
      _≤(∏j,‖m j‖)*geometricFrequency R k := parent_geometric_bound hR legs m k
      _≤(∏j,‖m j‖)*(normalizationBound R*referenceFrequency R k) :=
        mul_le_mul_of_nonneg_left hgeom (by positivity)
      _=_ := by ring

def raw {R : ℝ} (hR : 0≤R) (legs : Fin 3→Fin 4)
    (m : Fin 3→CubeFunction R) (k : E) : ℝ :=
  zeroExtension R (parentOutput R hR legs m) k/referenceFrequency R k

theorem raw_memLp {R : ℝ} (hR : 0≤R) (legs : Fin 3→Fin 4)
    (m : Fin 3→CubeFunction R) : MemLp (raw hR legs m) ∞ (cubeVolume R) := by
  apply memLp_top_of_bound
    ((zeroExtension_measurable R _).div
      (CollisionMarginalDensity.lossFrequency_measurable R referenceProfile_continuous.measurable)).aestronglyMeasurable
    (normalizationBound R*(∏j,‖m j‖))
  filter_upwards [ae_restrict_mem (measurable_cube R)] with k hk
  rw [zeroExtension_apply R _ ⟨k,hk⟩]
  exact parent_div_reference_bound hR legs m hk

def vector {R : ℝ} (hR : 0≤R) (legs : Fin 3→Fin 4)
    (m : Fin 3→CubeFunction R) : Lp ℝ ∞ (cubeVolume R) :=
  (raw_memLp hR legs m).toLp _

theorem vector_ae {R : ℝ} (hR : 0≤R) (legs : Fin 3→Fin 4)
    (m : Fin 3→CubeFunction R) :
    vector hR legs m=ᵐ[cubeVolume R] fun k=>
      (∫q,pointParent R legs q m∂fiberMeasure R k)/referenceFrequency R k := by
  filter_upwards [(raw_memLp hR legs m).coeFn_toLp,
    ae_restrict_mem (measurable_cube R)] with k he hk
  exact he.trans (by unfold raw; rw [zeroExtension_apply R _ ⟨k,hk⟩]; rfl)

def multilinear {R : ℝ} (hR : 0≤R) (legs : Fin 3→Fin 4) :
    MultilinearMap ℝ (fun _ : Fin 3=>CubeFunction R) (Lp ℝ ∞ (cubeVolume R)) where
  toFun := vector hR legs
  map_update_add' := by
    intro _ m i f g
    apply Lp.ext
    filter_upwards [vector_ae hR legs (update m i (f+g)),vector_ae hR legs (update m i f),
      vector_ae hR legs (update m i g),Lp.coeFn_add (vector hR legs (update m i f))
        (vector hR legs (update m i g))] with k hfg hf hg hs
    simp only [Pi.add_apply] at hs
    rw [hfg,hs,hf,hg]
    simp_rw [MultilinearMap.map_update_add]
    rw [integral_add (pointParent_integrable hR legs _ k) (pointParent_integrable hR legs _ k),add_div]
  map_update_smul' := by
    intro _ m i c f
    apply Lp.ext
    filter_upwards [vector_ae hR legs (update m i (c • f)),vector_ae hR legs (update m i f),
      Lp.coeFn_smul c (vector hR legs (update m i f))] with k hcf hf hs
    simp only [Pi.smul_apply,smul_eq_mul] at hs
    rw [hcf,hs,hf]
    simp_rw [MultilinearMap.map_update_smul]
    rw [integral_smul]
    simp only [smul_eq_mul]
    ring

theorem multilinear_bound {R : ℝ} (hR : 0≤R) (legs : Fin 3→Fin 4)
    (m : Fin 3→CubeFunction R) :
    ‖multilinear hR legs m‖≤normalizationBound R*(∏j,‖m j‖) := by
  letI := cubeVolume_finite R
  have hb : ∀ᵐk∂cubeVolume R,‖multilinear hR legs m k‖≤normalizationBound R*(∏j,‖m j‖) := by
    filter_upwards [vector_ae hR legs m,ae_restrict_mem (measurable_cube R)] with k he hk
    change ‖vector hR legs m k‖≤_
    rw [he]
    exact parent_div_reference_bound hR legs m hk
  simpa using Lp.norm_le_of_ae_bound
    (mul_nonneg (normalizationBound_pos R).le (Finset.prod_nonneg (fun _ _=>norm_nonneg _))) hb

def continuous {R : ℝ} (hR : 0≤R) (legs : Fin 3→Fin 4) :
    ContinuousMultilinearMap ℝ (fun _ : Fin 3=>CubeFunction R) (Lp ℝ ∞ (cubeVolume R)) :=
  (multilinear hR legs).mkContinuous (normalizationBound R) (multilinear_bound hR legs)

theorem continuous_norm_le {R : ℝ} (hR : 0≤R) (legs : Fin 3→Fin 4) :
    ‖continuous hR legs‖≤normalizationBound R :=
  MultilinearMap.mkContinuous_norm_le _ (normalizationBound_pos R).le _

theorem continuous_apply_ae {R : ℝ} (hR : 0≤R) (legs : Fin 3→Fin 4)
    (m : Fin 3→CubeFunction R) :
    continuous hR legs m=ᵐ[cubeVolume R] fun k=>
      (∫q,pointParent R legs q m∂fiberMeasure R k)/referenceFrequency R k := vector_ae hR legs m

end
end Resonance.NormalizedFiberMultilinear
