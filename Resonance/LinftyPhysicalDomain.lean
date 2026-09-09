import Resonance.AmbientLinftyCompact
import Resonance.ReferenceMomentFunctionals

/-! A genuine one-frequency inverse maps the original bounded forcing
coordinate into the full physical H_nu domain.  The inverse frequency is
not bounded; its square integrability is derived from the actual corner
integrability and the actual two-frequency comparison. -/
open MeasureTheory Set Filter
open scoped ENNReal Topology
namespace Resonance.LinftyPhysicalDomain
noncomputable section
set_option maxHeartbeats 1000000
open ResonantMeasure WeightedJointMeasure CollisionFrequency ActualPairNormalization
open ReferenceFrequencySpace ActualFrequencyRatio

theorem loss_positive_ae {R : ℝ} (hR : 0 < R)
    {θ : Thermodynamics.Parameter} (hθ : θ ∈ Thermodynamics.positiveDomain R) :
    ∀ᵐ k ∂cubeVolume R, 0 < lossFrequency R (profile θ) k := by
  obtain ⟨a,ha,hb⟩ := loss_reference_lower hR hθ
  filter_upwards [CornerInverseFrequency.referenceFrequency_positive_ae hR,
    ae_restrict_mem (FiberContinuity.cube_isClosed R).measurableSet] with k hk hkc
  exact (mul_pos ha hk).trans_le (hb k hkc)

theorem inverse_loss_memLp {R : ℝ} (hR : 0 < R)
    {θ : Thermodynamics.Parameter} (hθ : θ ∈ Thermodynamics.positiveDomain R) :
    MemLp (fun k => (lossFrequency R (profile θ) k)⁻¹) 2 (referenceMeasure R) := by
  obtain ⟨a,ha,hb⟩ := loss_reference_lower hR hθ
  apply (ReferenceMomentFunctionals.inverse_memLp hR).of_le_mul
    (CollisionMarginalDensity.lossFrequency_measurable R (profile_measurable θ)).inv.aestronglyMeasurable
  have hac := (reference_volume_equivalent hR).2
  filter_upwards [hac.ae_le (CornerInverseFrequency.referenceFrequency_positive_ae hR),
    reference_support R] with k hk hkc
  have hl := hb k hkc
  have hp : 0 < lossFrequency R (profile θ) k := (mul_pos ha hk).trans_le hl
  rw [Real.norm_of_nonneg (inv_nonneg.mpr hp.le),Real.norm_of_nonneg (inv_nonneg.mpr hk.le)]
  exact (inv_anti₀ (mul_pos ha hk) hl).trans_eq (by rw [mul_inv])

def inverseLossVector {R : ℝ} (hR : 0 < R)
    {θ : Thermodynamics.Parameter} (hθ : θ ∈ Thermodynamics.positiveDomain R) : Space R :=
  (inverse_loss_memLp hR hθ).toLp _

theorem inverseLossVector_ae {R : ℝ} (hR : 0 < R)
    {θ : Thermodynamics.Parameter} (hθ : θ ∈ Thermodynamics.positiveDomain R) :
    inverseLossVector hR hθ =ᵐ[referenceMeasure R]
      (fun k => (lossFrequency R (profile θ) k)⁻¹) :=
  (inverse_loss_memLp hR hθ).coeFn_toLp

theorem divided_memLp {R : ℝ} (hR : 0 < R)
    {θ : Thermodynamics.Parameter} (hθ : θ ∈ Thermodynamics.positiveDomain R)
    (f : Lp ℝ ∞ (cubeVolume R)) :
    MemLp (fun k => f k/(lossFrequency R (profile θ) k)) 2 (referenceMeasure R) := by
  apply (inverse_loss_memLp hR hθ).of_le_mul
    ((Lp.stronglyMeasurable f).measurable.div
      (CollisionMarginalDensity.lossFrequency_measurable R (profile_measurable θ))).aestronglyMeasurable
  filter_upwards [(reference_volume_equivalent hR).2.ae_le (LinftyRowOperator.ae_norm_bound f)] with k hk
  rw [div_eq_mul_inv,norm_mul]
  exact mul_le_mul_of_nonneg_right hk (norm_nonneg _)

def divideVector {R : ℝ} (hR : 0 < R)
    {θ : Thermodynamics.Parameter} (hθ : θ ∈ Thermodynamics.positiveDomain R)
    (f : Lp ℝ ∞ (cubeVolume R)) : Space R := (divided_memLp hR hθ f).toLp _

theorem divideVector_ae {R : ℝ} (hR : 0 < R)
    {θ : Thermodynamics.Parameter} (hθ : θ ∈ Thermodynamics.positiveDomain R)
    (f : Lp ℝ ∞ (cubeVolume R)) :
    divideVector hR hθ f =ᵐ[referenceMeasure R]
      (fun k => f k/(lossFrequency R (profile θ) k)) := (divided_memLp hR hθ f).coeFn_toLp

theorem divideVector_add {R : ℝ} (hR : 0 < R)
    {θ : Thermodynamics.Parameter} (hθ : θ ∈ Thermodynamics.positiveDomain R)
    (f g : Lp ℝ ∞ (cubeVolume R)) :
    divideVector hR hθ (f+g)=divideVector hR hθ f+divideVector hR hθ g := by
  apply Lp.ext
  filter_upwards [divideVector_ae hR hθ (f+g),divideVector_ae hR hθ f,divideVector_ae hR hθ g,
    Lp.coeFn_add (divideVector hR hθ f) (divideVector hR hθ g),
    (reference_volume_equivalent hR).2.ae_eq (Lp.coeFn_add f g)] with k hfg hf hg ho hi
  simp only [Pi.add_apply] at hi ho
  rw [hfg,ho,hi,hf,hg,add_div]

theorem divideVector_smul {R : ℝ} (hR : 0 < R)
    {θ : Thermodynamics.Parameter} (hθ : θ ∈ Thermodynamics.positiveDomain R)
    (a : ℝ) (f : Lp ℝ ∞ (cubeVolume R)) :
    divideVector hR hθ (a • f)=a • divideVector hR hθ f := by
  apply Lp.ext
  filter_upwards [divideVector_ae hR hθ (a • f),divideVector_ae hR hθ f,
    Lp.coeFn_smul a (divideVector hR hθ f),
    (reference_volume_equivalent hR).2.ae_eq (Lp.coeFn_smul a f)] with k haf hf ho hi
  simp only [Pi.smul_apply,smul_eq_mul] at hi ho
  rw [haf,ho,hi,hf,mul_div_assoc]

theorem divideVector_bound {R : ℝ} (hR : 0 < R)
    {θ : Thermodynamics.Parameter} (hθ : θ ∈ Thermodynamics.positiveDomain R)
    (f : Lp ℝ ∞ (cubeVolume R)) :
    ‖divideVector hR hθ f‖ ≤ ‖inverseLossVector hR hθ‖*‖f‖ := by
  rw [mul_comm]
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [divideVector_ae hR hθ f,inverseLossVector_ae hR hθ,
    (reference_volume_equivalent hR).2.ae_le (LinftyRowOperator.ae_norm_bound f)] with k hu hv hf
  rw [hu,hv,div_eq_mul_inv,norm_mul]
  exact mul_le_mul_of_nonneg_right hf (norm_nonneg _)

def divideLinear {R : ℝ} (hR : 0 < R)
    {θ : Thermodynamics.Parameter} (hθ : θ ∈ Thermodynamics.positiveDomain R) :
    Lp ℝ ∞ (cubeVolume R) →ₗ[ℝ] Space R where
  toFun := divideVector hR hθ
  map_add' := divideVector_add hR hθ
  map_smul' := divideVector_smul hR hθ

def divide {R : ℝ} (hR : 0 < R)
    {θ : Thermodynamics.Parameter} (hθ : θ ∈ Thermodynamics.positiveDomain R) :
    Lp ℝ ∞ (cubeVolume R) →L[ℝ] Space R :=
  (divideLinear hR hθ).mkContinuous ‖inverseLossVector hR hθ‖ (divideVector_bound hR hθ)

theorem divide_ae_volume {R : ℝ} (hR : 0 < R)
    {θ : Thermodynamics.Parameter} (hθ : θ ∈ Thermodynamics.positiveDomain R)
    (f : Lp ℝ ∞ (cubeVolume R)) :
    divide hR hθ f =ᵐ[cubeVolume R] (fun k => f k/(lossFrequency R (profile θ) k)) :=
  (reference_volume_equivalent hR).1.ae_eq (divideVector_ae hR hθ f)

theorem frequency_divide_ae {R : ℝ} (hR : 0 < R)
    {θ : Thermodynamics.Parameter} (hθ : θ ∈ Thermodynamics.positiveDomain R)
    (f : Lp ℝ ∞ (cubeVolume R)) :
    (fun k => lossFrequency R (profile θ) k*divide hR hθ f k)=ᵐ[cubeVolume R] f := by
  filter_upwards [divide_ae_volume hR hθ f,loss_positive_ae hR hθ] with k hu hp
  rw [hu,mul_div_cancel₀ _ hp.ne']

theorem divide_injective {R : ℝ} (hR : 0 < R)
    {θ : Thermodynamics.Parameter} (hθ : θ ∈ Thermodynamics.positiveDomain R) :
    Function.Injective (divide hR hθ) := by
  intro f g hfg
  apply Lp.ext
  filter_upwards [frequency_divide_ae hR hθ f,frequency_divide_ae hR hθ g] with k hf hg
  rw [hfg] at hf
  exact hf.symm.trans hg

end
end Resonance.LinftyPhysicalDomain
