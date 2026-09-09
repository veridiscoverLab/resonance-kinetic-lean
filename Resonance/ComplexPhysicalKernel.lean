import Resonance.ComplexPhysicalForm
import Resonance.ComplexLpLinear

/-! The complete complex five-mode kernel and uniform distance-to-kernel
coercivity for the original physical form. -/
open MeasureTheory Set
namespace Resonance.ComplexPhysicalKernel
noncomputable section
open ResonantMeasure WeightedJointMeasure Thermodynamics ReferenceFrequencySpace
open PhysicalFrequencyCoordinates ComplexLpDecomposition ComplexLpLinear
open ComplexPhysicalForm ComplexFiveInvariants

def fullDifference {R : ℝ} (hR : 0≤R) {θ : Parameter} (hθ : θ∈positiveDomain R) :
    ComplexSpace R→L[ℂ]Lp ℂ 2 (jointMeasure R θ) := complexLift (physicalDifference hR hθ)

theorem fullDifference_eq {R : ℝ} (hR : 0≤R) {θ : Parameter} (hθ : θ∈positiveDomain R)
    (u : ComplexSpace R) : fullDifference hR hθ u=difference hR hθ u := rfl

theorem coefficient_parts_iff {R : ℝ} (hR : 0<R) {θ : Parameter}
    (u : ComplexSpace R) (b : ComplexCoefficients) :
    ((u : E→ℂ)=ᵐ[volume.restrict (cube R)] (fun k=>(profile θ k : ℂ)*evaluateComplex b k)) ↔
    ((realPart (referenceMeasure R) u : E→ℝ)=ᵐ[volume.restrict (cube R)]
      (fun k=>profile θ k*QuadraticPointwiseClosure.evaluate b.1 k)) ∧
    ((imagPart (referenceMeasure R) u : E→ℝ)=ᵐ[volume.restrict (cube R)]
      (fun k=>profile θ k*QuadraticPointwiseClosure.evaluate b.2 k)) := by
  have hr := (reference_volume_equivalent hR).1.ae_eq (realPart_ae u)
  have hi := (reference_volume_equivalent hR).1.ae_eq (imagPart_ae u)
  constructor
  · intro hb
    constructor
    · filter_upwards [hb,hr] with k hk hkr
      rw [hkr,hk]
      simp [evaluateComplex]
    · filter_upwards [hb,hi] with k hk hki
      rw [hki,hk]
      simp [evaluateComplex]
  · rintro ⟨hbr,hbi⟩
    filter_upwards [hbr,hbi,hr,hi] with k h1 h2 h3 h4
    apply Complex.ext
    · simpa [evaluateComplex] using h3.symm.trans h1
    · simpa [evaluateComplex] using h4.symm.trans h2

theorem complex_kernel_unique {R : ℝ} (hR : 0<R) {θ : Parameter}
    (hθ : θ∈positiveDomain R) (u : ComplexSpace R) (hu : u∈(fullDifference hR.le hθ).ker) :
    ∃!b : ComplexCoefficients,(u : E→ℂ)=ᵐ[volume.restrict (cube R)]
      (fun k=>(profile θ k : ℂ)*evaluateComplex b k) := by
  have hz : complexLift (physicalDifference hR.le hθ) u=0 := hu
  obtain ⟨hr,hi⟩ := (complexLift_zero_iff (physicalDifference hR.le hθ) u).mp hz
  obtain ⟨a,ha,hauniq⟩ := (PhysicalWeightedCoercivity.physical_kernel_classification hR hθ
    (realPart (referenceMeasure R) u)).mp hr
  obtain ⟨b,hb,hbuniq⟩ := (PhysicalWeightedCoercivity.physical_kernel_classification hR hθ
    (imagPart (referenceMeasure R) u)).mp hi
  refine ⟨(a,b),(coefficient_parts_iff hR u (a,b)).mpr ⟨ha,hb⟩,?_⟩
  intro c hc
  obtain ⟨hc1,hc2⟩ := (coefficient_parts_iff hR u c).mp hc
  exact Prod.ext (hauniq c.1 hc1) (hbuniq c.2 hc2)

theorem complex_kernel_iff {R : ℝ} (hR : 0<R) {θ : Parameter}
    (hθ : θ∈positiveDomain R) (u : ComplexSpace R) :
    u∈(fullDifference hR.le hθ).ker ↔ ∃b : ComplexCoefficients,
      (u : E→ℂ)=ᵐ[volume.restrict (cube R)] (fun k=>(profile θ k : ℂ)*evaluateComplex b k) := by
  constructor
  · intro hu
    exact (complex_kernel_unique hR hθ u hu).exists
  · rintro ⟨b,hb⟩
    obtain ⟨hr,hi⟩ := (coefficient_parts_iff hR u b).mp hb
    apply (complexLift_zero_iff (physicalDifference hR.le hθ) u).mpr
    exact ⟨(PhysicalProjectionKernel.physical_kernel_iff_exists hR hθ _).mpr ⟨b.1,hr⟩,
      (PhysicalProjectionKernel.physical_kernel_iff_exists hR hθ _).mpr ⟨b.2,hi⟩⟩

theorem complex_projection_residual_le {H J : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] [NormedAddCommGroup J] [NormedSpace ℂ J]
    (T : H→L[ℂ]J) (f g : H) (hg : g∈T.ker) :
    ‖f-T.ker.starProjection f‖≤‖f-g‖ := by
  have h := T.kerᗮ.norm_starProjection_apply_le (f-g)
  rw [Submodule.starProjection_orthogonal',ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.one_apply,map_sub,T.ker.starProjection_eq_self_iff.mpr hg] at h
  convert h using 1
  congr 1
  abel

theorem complex_uniform_coercivity {R : ℝ} (hR : 0<R) {K : Set Parameter}
    (hK : IsCompact K) (hpos : K⊆positiveDomain R) :
    ∃δ : ℝ,0<δ ∧ ∀θ,(hθ : θ∈K) → ∀u : ComplexSpace R,
      δ*‖u-(fullDifference hR.le (hpos hθ)).ker.starProjection u‖^2≤
        (form hR.le (hpos hθ) u u).re := by
  obtain ⟨δ,hδ,hgap⟩ := PhysicalWeightedCoercivity.physical_uniform_coercivity hR hK hpos
  refine ⟨δ,hδ,?_⟩
  intro θ hθ u
  let T := physicalDifference hR.le (hpos hθ)
  let P := T.ker.starProjection
  have hp : lift P u∈(fullDifference hR.le (hpos hθ)).ker := by
    apply (complexLift_zero_iff T (lift P u)).mpr
    rw [realPart_lift,imagPart_lift]
    exact ⟨T.ker.starProjection_apply_mem _,T.ker.starProjection_apply_mem _⟩
  have hd := complex_projection_residual_le (fullDifference hR.le (hpos hθ)) u (lift P u) hp
  have hs := mul_self_le_mul_self (norm_nonneg _) hd
  have hgr := hgap θ hθ (realPart (referenceMeasure R) u)
  have hgi := hgap θ hθ (imagPart (referenceMeasure R) u)
  have hn := lift_sub_norm_square P u
  rw [form_real_parts]
  change ‖u-lift P u‖^2=‖realPart (referenceMeasure R) u-P (realPart (referenceMeasure R) u)‖^2+
    ‖imagPart (referenceMeasure R) u-P (imagPart (referenceMeasure R) u)‖^2 at hn
  change δ*‖realPart (referenceMeasure R) u-P (realPart (referenceMeasure R) u)‖^2≤_ at hgr
  change δ*‖imagPart (referenceMeasure R) u-P (imagPart (referenceMeasure R) u)‖^2≤_ at hgi
  nlinarith [mul_nonneg hδ.le (show 0≤‖u-lift P u‖^2-
    ‖u-(fullDifference hR.le (hpos hθ)).ker.starProjection u‖^2 by nlinarith)]

end
end Resonance.ComplexPhysicalKernel
