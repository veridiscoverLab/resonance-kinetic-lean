import Resonance.SpacetimeCurrentReturn
import Resonance.PhysicalFiveBasis

/-! Actual unweighted physical tests enter the reference-frequency space
through its original bounded density. Multiplication by the original N then
cancels the reciprocal factor in the complete difference. This constructs
the physical transpose without confusing it with the reference Riesz metric. -/
open Set MeasureTheory MeasureTheory.Measure
open scoped ENNReal
namespace Resonance.SpacetimePhysicalTests
noncomputable section
set_option maxHeartbeats 2000000
open ResonantMeasure Thermodynamics WeightedJointMeasure CollisionFrequency
open SpacetimePairing SpacetimeReference SpacetimeDifference LpOperators

abbrev PhysicalSpace (R T : ℝ) := Lp ℝ 2 (sourceMeasure R T)

theorem reference_domination {R : ℝ} (hR : 0 ≤ R) (T : ℝ) :
    ∃ C : ℝ≥0∞, C ≠ ∞ ∧ reference R T ≤ C • sourceMeasure R T := by
  obtain ⟨C,hC⟩ := PhysicalFiveBasis.continuous_cube_bounded (referenceFrequency_continuousOn hR)
  have hd : ReferenceFrequencySpace.referenceMeasure R ≤
      ENNReal.ofReal C • ActualPairNormalization.cubeVolume R := by
    rw [ReferenceFrequencySpace.referenceMeasure,←withDensity_const]
    apply withDensity_mono
    filter_upwards [ae_restrict_mem (measurable_cube R)] with k hk
    apply ENNReal.ofReal_le_ofReal
    exact (le_abs_self _).trans (by simpa only [Real.norm_eq_abs] using hC k hk)
  letI := SpacetimeReference.reference_finite hR
  exact ⟨ENNReal.ofReal C,ENNReal.ofReal_ne_top,product_domination (baseMeasure T) hd⟩

def physicalInclusion {R : ℝ} (hR : 0 ≤ R) (T : ℝ) : PhysicalSpace R T →L[ℝ] Space R T :=
  changeCLM (Classical.choose_spec (reference_domination hR T)).1
    (Classical.choose_spec (reference_domination hR T)).2

theorem physicalInclusion_ae {R : ℝ} (hR : 0 ≤ R) (T : ℝ) (u : PhysicalSpace R T) :
    (physicalInclusion hR T u : Source → ℝ) =ᵐ[reference R T] u :=
  changeMeasure_ae (Classical.choose_spec (reference_domination hR T)).1
    (Classical.choose_spec (reference_domination hR T)).2 u

def profileField (θ : Base → Parameter) (z : Source) : ℝ := profile (θ z.1) z.2

theorem divide_product_ae {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f g q : α → ℝ} (he : f =ᵐ[μ] (fun x => g x * q x))
    (hq : ∀ᵐ x ∂μ, q x ≠ 0) : (fun x => f x / q x) =ᵐ[μ] g := by
  filter_upwards [he,hq] with x hx hqx
  rw [hx,mul_div_cancel_right₀ _ hqx]

theorem normalized_difference_ae {R : ℝ} (hR : 0 < R) (T : ℝ)
    (θ : Base → Parameter) {f g : Source → ℝ}
    (he : (fun z => f z / profileField θ z) =ᵐ[reference R T] g) :
    physicalRaw (θ := θ) f =ᵐ[SpacetimeRJMeasure.measure R T θ] rawDifference g := by
  filter_upwards [(SpacetimeProfileBounds.weighted_leg_reference hR T θ 0).ae_eq he,
    (SpacetimeProfileBounds.weighted_leg_reference hR T θ 1).ae_eq he,
    (SpacetimeProfileBounds.weighted_leg_reference hR T θ 2).ae_eq he,
    (SpacetimeProfileBounds.weighted_leg_reference hR T θ 3).ae_eq he] with p h0 h1 h2 h3
  simp only [Function.comp_def,profileField,leg] at h0 h1 h2 h3
  simp only [physicalRaw,rawDifference,leg,h0,h1,h2,h3]

theorem profileField_memLp {R : ℝ} (hR : 0 ≤ R) (T : ℝ)
    {K : Set Parameter} (hK : IsCompact K) (hpos : K ⊆ positiveDomain R)
    {θ : Base → Parameter} (hm : Measurable θ) (hθ : ∀ᵐ a ∂baseMeasure T, θ a ∈ K) :
    MemLp (profileField θ) ∞ (reference R T) := by
  obtain ⟨m,M,hm0,hM,hb⟩ := JointWeightComparison.compact_profile_bounds hR hK hpos
  apply memLp_top_of_bound
    (SpacetimeRJMeasure.joint_profile_measurable.comp
      ((hm.comp measurable_fst).prodMk measurable_snd)).aestronglyMeasurable M
  have ht : ∀ᵐ z ∂reference R T, θ z.1 ∈ K := quasiMeasurePreserving_fst.ae hθ
  have hk : ∀ᵐ z ∂reference R T, z.2 ∈ cube R :=
    quasiMeasurePreserving_snd.ae (ReferenceFrequencySpace.reference_support R)
  filter_upwards [ht,hk] with z ht hk
  change |profile (θ z.1) z.2| ≤ M
  rw [abs_of_pos (profile_pos (hpos ht) hk)]
  exact (hb (θ z.1) ht z.2 hk).2

variable {R : ℝ} (hR : 0 < R) (T : ℝ) {K : Set Parameter}
  (hK : IsCompact K) (hpos : K ⊆ positiveDomain R)
  {θ : Base → Parameter} (hm : Measurable θ) (hθ : ∀ᵐ a ∂baseMeasure T, θ a ∈ K)

def physicalTest : PhysicalSpace R T →L[ℝ] Space R T :=
  (multiplyCLM (profileField_memLp hR.le T hK hpos hm hθ)).comp (physicalInclusion hR.le T)

theorem physicalTest_ae (u : PhysicalSpace R T) :
    physicalTest hR T hK hpos hm hθ u =ᵐ[reference R T] (fun z => u z * profileField θ z) := by
  filter_upwards [multiply_ae (profileField_memLp hR.le T hK hpos hm hθ)
    (physicalInclusion hR.le T u),physicalInclusion_ae hR.le T u] with z hm hi
  change multiply (profileField_memLp hR.le T hK hpos ‹Measurable θ› hθ)
    (physicalInclusion hR.le T u) z = _
  rw [hm,hi]

def physicalDifference : PhysicalSpace R T →L[ℝ] Lp ℝ 2 (SpacetimeRJMeasure.measure R T θ) :=
  (SpacetimeDifference.physicalDifference hR T hK hpos hm hθ).comp
    (physicalTest hR T hK hpos hm hθ)

theorem physicalDifference_ae (u : PhysicalSpace R T) :
    physicalDifference hR T hK hpos hm hθ u =ᵐ[SpacetimeRJMeasure.measure R T θ]
      rawDifference (u : Source → ℝ) := by
  have hu := physicalTest_ae hR T hK hpos hm hθ u
  have ht : ∀ᵐ z ∂reference R T, θ z.1 ∈ K := quasiMeasurePreserving_fst.ae hθ
  have hk : ∀ᵐ z ∂reference R T, z.2 ∈ cube R :=
    quasiMeasurePreserving_snd.ae (ReferenceFrequencySpace.reference_support R)
  have hn : ∀ᵐ z ∂reference R T, profileField θ z ≠ 0 := by
    filter_upwards [ht,hk] with z ht hk
    exact (profile_pos (hpos ht) hk).ne'
  have hd := divide_product_ae hu hn
  have hh := normalized_difference_ae hR T θ
    (f := (physicalTest hR T hK hpos hm hθ u : Source → ℝ))
    (g := (u : Source → ℝ)) hd
  have hr := SpacetimeDifference.physicalDifference_ae hR T hK hpos hm hθ
    (physicalTest hR T hK hpos hm hθ u)
  unfold physicalDifference
  rw [ContinuousLinearMap.comp_apply]
  exact hr.trans hh

end
end Resonance.SpacetimePhysicalTests
