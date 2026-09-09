import Resonance.ResonantMeasure

/-! The original common pairing measure has full support on every interior
admissible parameter chart. Thus a continuous collision invariant satisfies
the complete collision equation at every interior admissible quartet. -/
open Set MeasureTheory Metric
open scoped ENNReal NNReal Topology

namespace Resonance.ContinuousCollisionInvariants
noncomputable section
open ResonantMeasure

def openCube (R : ℝ) : Set E := {k | ∀ j : Fin 3, |k j| < R}

theorem openCube_isOpen (R : ℝ) : IsOpen (openCube R) := by
  change IsOpen {k : E | ∀ j : Fin 3, |k j| < R}
  simp only [setOf_forall]
  apply isOpen_iInter_of_finite
  intro j
  exact isOpen_lt (by fun_prop) continuous_const

theorem openCube_subset_cube (R : ℝ) : openCube R ⊆ cube R :=
  fun _ h j => (h j).le

def interiorAllowed (R : ℝ) : Set Parameters := {p | ∀ i : Fin 4, paired p i ∈ openCube R}

theorem interiorAllowed_isOpen (R : ℝ) : IsOpen (interiorAllowed R) := by
  simp only [interiorAllowed, setOf_forall]
  apply isOpen_iInter_of_finite
  intro i
  exact (openCube_isOpen R).preimage ((continuous_apply i).comp continuous_paired)

theorem interiorAllowed_subset_allowed (R : ℝ) : interiorAllowed R ⊆ allowed R :=
  fun _ h i => openCube_subset_cube R (h i)

instance surface_openPos : Measure.IsOpenPosMeasure surface := by
  unfold surface
  infer_instance

instance radial_openPos : Measure.IsOpenPosMeasure radial := by
  let μr : Measure Radius := (volume : Measure ℝ).comap Subtype.val
  letI : Measure.IsOpenPosMeasure μr :=
    Measure.IsOpenPosMeasure.comap volume isOpen_Ioi.isOpenEmbedding_subtypeVal
  have hac : μr ≪ radial := by
    unfold radial Measure.volumeIoiPow
    apply withDensity_absolutelyContinuous' (by fun_prop)
    exact ae_of_all _ (fun r => ne_of_gt (ENNReal.ofReal_pos.mpr (pow_pos r.property 3)))
  exact hac.isOpenPosMeasure

instance base_openPos : Measure.IsOpenPosMeasure base := by
  letI : Measure.IsOpenPosMeasure (surface.prod surface) := by infer_instance
  letI : Measure.IsOpenPosMeasure (radial.prod (surface.prod surface)) := by infer_instance
  unfold base
  infer_instance

def invariant (R : ℝ) (f : E → ℝ) : Prop :=
  ∀ᵐ q ∂pairingMeasure R, f (q 0) + f (q 1) = f (q 2) + f (q 3)

theorem invariant_parameter_ae {R : ℝ} {f : E → ℝ} (hf : invariant R f) :
    ∀ᵐ p ∂base.restrict (interiorAllowed R),
      f (paired p 0) + f (paired p 1) = f (paired p 2) + f (paired p 3) := by
  have hp := ae_of_ae_map continuous_paired.measurable.aemeasurable hf
  change ∀ᵐ p ∂(2 : ℝ≥0∞) • base.restrict (allowed R),
    f (paired p 0) + f (paired p 1) = f (paired p 2) + f (paired p 3) at hp
  have hp' : ∀ᵐ p ∂base.restrict (allowed R),
      f (paired p 0) + f (paired p 1) = f (paired p 2) + f (paired p 3) :=
    (Measure.ae_ennreal_smul_measure_iff (by norm_num : (2 : ℝ≥0∞) ≠ 0)).mp hp
  exact ae_restrict_of_ae_restrict_of_subset (interiorAllowed_subset_allowed R) hp'

theorem continuous_invariant_every_interior_pair {R : ℝ} {f : E → ℝ}
    (hfc : ContinuousOn f (openCube R)) (hf : invariant R f)
    (p : Parameters) (hp : p ∈ interiorAllowed R) :
    f (paired p 0) + f (paired p 1) = f (paired p 2) + f (paired p 3) := by
  have hc (i : Fin 4) : ContinuousOn (fun p => f (paired p i)) (interiorAllowed R) :=
    hfc.comp ((continuous_apply i).comp continuous_paired).continuousOn (fun _ h => h i)
  exact Measure.eqOn_open_of_ae_eq (invariant_parameter_ae hf) (interiorAllowed_isOpen R)
    ((hc 0).add (hc 1)) ((hc 2).add (hc 3)) hp

theorem continuous_invariant_pair_sum {R : ℝ} {f : E → ℝ}
    (hfc : ContinuousOn f (openCube R)) (hf : invariant R f)
    (V : E) (r : ℝ) (hr : 0 < r) (σ τ : Sphere)
    (h0 : V+r • (σ : E) ∈ openCube R) (h1 : V-r • (σ : E) ∈ openCube R)
    (h2 : V+r • (τ : E) ∈ openCube R) (h3 : V-r • (τ : E) ∈ openCube R) :
    f (V+r • (σ : E)) + f (V-r • (σ : E)) =
      f (V+r • (τ : E)) + f (V-r • (τ : E)) := by
  apply continuous_invariant_every_interior_pair hfc hf (V,⟨r,hr⟩,σ,τ)
  intro i
  fin_cases i
  · exact h0
  · exact h1
  · exact h2
  · exact h3

def normalizedDirection (v : E) (hv : v ≠ 0) : Sphere :=
  ⟨‖v‖⁻¹ • v, by
    simp only [Sphere, mem_sphere, dist_zero_right, norm_smul, Real.norm_eq_abs,
      abs_inv, abs_of_nonneg (norm_nonneg v)]
    exact inv_mul_cancel₀ (norm_ne_zero_iff.mpr hv)⟩

theorem radius_normalizedDirection (v : E) (hv : v ≠ 0) :
    ‖v‖ • (normalizedDirection v hv : E) = v := by
  change ‖v‖ • (‖v‖⁻¹ • v) = v
  rw [smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr hv), one_smul]

theorem continuous_invariant_equal_norm_pair {R : ℝ} {f : E → ℝ}
    (hfc : ContinuousOn f (openCube R)) (hf : invariant R f)
    (V v w : E) (hv : v ≠ 0) (he : ‖v‖ = ‖w‖)
    (h0 : V+v ∈ openCube R) (h1 : V-v ∈ openCube R)
    (h2 : V+w ∈ openCube R) (h3 : V-w ∈ openCube R) :
    f (V+v) + f (V-v) = f (V+w) + f (V-w) := by
  have hw : w ≠ 0 := by
    intro h
    rw [h,norm_zero] at he
    exact hv (norm_eq_zero.mp he)
  have ev := radius_normalizedDirection v hv
  have ew : ‖v‖ • (normalizedDirection w hw : E) = w := by
    rw [he]
    exact radius_normalizedDirection w hw
  have h := continuous_invariant_pair_sum hfc hf V ‖v‖ (norm_pos_iff.mpr hv)
    (normalizedDirection v hv) (normalizedDirection w hw)
    (by rwa [ev]) (by rwa [ev]) (by rwa [ew]) (by rwa [ew])
  simpa only [ev,ew] using h

end
end Resonance.ContinuousCollisionInvariants
