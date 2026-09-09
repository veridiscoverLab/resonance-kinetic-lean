import Resonance.ShiftedOperatorLimit

/-! Operator-norm continuity of the genuine division map at zero loss shift.
The dominating vector is the actual inverse loss in the full H_nu space. -/
open MeasureTheory Set Filter
open scoped ENNReal Topology
namespace Resonance.ShiftedDivideLimit
noncomputable section
set_option maxHeartbeats 1600000
open ResonantMeasure Thermodynamics WeightedJointMeasure CollisionFrequency
open ActualPairNormalization ReferenceFrequencySpace LinftyPhysicalDomain
open PositiveLossShift ShiftRowVanishing

theorem error_memLp {R : ℝ} (hR : 0<R) {θ : Parameter}
    (hθ : θ∈positiveDomain R) (n : ℕ) :
    MemLp (fun k=>(lossFrequency R (profile θ) k)⁻¹*cutoff R θ n k)
      2 (referenceMeasure R) := by
  apply (inverse_loss_memLp hR hθ).of_le
    ((CollisionMarginalDensity.lossFrequency_measurable R (profile_measurable θ)).inv.mul
      (cutoff_measurable R θ n)).aestronglyMeasurable
  filter_upwards [reference_support R] with k hk
  rw [norm_mul,Real.norm_of_nonneg (cutoff_bounds hR hθ n hk).1]
  exact mul_le_of_le_one_right (norm_nonneg _) (cutoff_bounds hR hθ n hk).2

def errorVector {R : ℝ} (hR : 0<R) {θ : Parameter}
    (hθ : θ∈positiveDomain R) (n : ℕ) : Space R := (error_memLp hR hθ n).toLp _

theorem errorVector_ae {R : ℝ} (hR : 0<R) {θ : Parameter}
    (hθ : θ∈positiveDomain R) (n : ℕ) :
    errorVector hR hθ n=ᵐ[referenceMeasure R]
      (fun k=>(lossFrequency R (profile θ) k)⁻¹*cutoff R θ n k) :=
  (error_memLp hR hθ n).coeFn_toLp

theorem errorVector_norm_tendsto {R : ℝ} (hR : 0<R) {θ : Parameter}
    (hθ : θ∈positiveDomain R) :
    Tendsto (fun n=>‖errorVector hR hθ n‖) atTop (𝓝 0) := by
  have hi := (inverse_loss_memLp hR hθ).integrable_sq
  have ht : Tendsto (fun n=>∫k,((lossFrequency R (profile θ) k)⁻¹*cutoff R θ n k)^2
      ∂referenceMeasure R) atTop (𝓝 (∫_k,(0:ℝ)∂referenceMeasure R)) := by
    apply tendsto_integral_of_dominated_convergence
      (fun k=>((lossFrequency R (profile θ) k)⁻¹)^2)
    · intro n
      exact ((error_memLp hR hθ n).aestronglyMeasurable.pow 2)
    · exact hi
    · intro n
      filter_upwards [reference_support R] with k hk
      rw [Real.norm_of_nonneg (sq_nonneg _),mul_pow]
      have hc := cutoff_bounds hR hθ n hk
      have hs : (cutoff R θ n k)^2≤1 := by nlinarith
      exact mul_le_of_le_one_right (sq_nonneg _) hs
    · filter_upwards [(reference_volume_equivalent hR).2.ae_le (cutoff_tendsto hR hθ)] with k hk
      simpa using (tendsto_const_nhds.mul hk).pow 2
  have hs : Tendsto (fun n=>‖errorVector hR hθ n‖^2) atTop (𝓝 0) := by
    have he (n : ℕ) : ‖errorVector hR hθ n‖^2=
        ∫k,((lossFrequency R (profile θ) k)⁻¹*cutoff R θ n k)^2∂referenceMeasure R := by
      rw [L2KernelPairing.norm_sq_integral]
      apply integral_congr_ae
      filter_upwards [errorVector_ae hR hθ n] with k hk
      rw [hk]
    simp_rw [he]
    simpa using ht
  have hh := Real.continuous_sqrt.continuousAt.tendsto.comp hs
  simpa only [Function.comp_def,Real.sqrt_sq (norm_nonneg _),Real.sqrt_zero] using hh

theorem shiftedDivide_error_bound {R : ℝ} (hR : 0<R) {θ : Parameter}
    (hθ : θ∈positiveDomain R) (n : ℕ) {z : ℝ} (hz : 0≤z) (hzn : z ≤ scale n) :
    ‖shiftedDivide hR hθ hz-divide hR hθ‖≤‖errorVector hR hθ n‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro F
  rw [mul_comm]
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [Lp.coeFn_sub (shiftedDivide hR hθ hz F) (divide hR hθ F),
    (reference_volume_equivalent hR).2.ae_eq (shiftedDivide_ae hR hθ hz F),
    divideVector_ae hR hθ F,errorVector_ae hR hθ n,
    (reference_volume_equivalent hR).2.ae_le (LinftyRowOperator.ae_norm_bound F),
    (reference_volume_equivalent hR).2.ae_le (loss_positive_ae hR hθ),reference_support R]
      with k hs hzv h0 he hf hn hk
  change (shiftedDivide hR hθ hz F-divide hR hθ F) k=
    shiftedDivide hR hθ hz F k-divide hR hθ F k at hs
  change divide hR hθ F k=F k/lossFrequency R (profile θ) k at h0
  change ‖(shiftedDivide hR hθ hz F-divide hR hθ F) k‖≤_
  rw [hs,hzv,h0,he]
  have hd := (add_pos_of_pos_of_nonneg hn hz).ne'
  have heq : F k/(lossFrequency R (profile θ) k+z)-F k/lossFrequency R (profile θ) k=
      -(F k*(lossFrequency R (profile θ) k)⁻¹)*(z/(lossFrequency R (profile θ) k+z)) := by
    field_simp
    ring
  have hgap : z/(lossFrequency R (profile θ) k+z)≤cutoff R θ n k := by
    unfold cutoff
    apply (div_le_div_iff₀ (add_pos_of_pos_of_nonneg hn hz) (add_pos hn (scale_pos n))).mpr
    nlinarith
  have hg0 : 0≤z/(lossFrequency R (profile θ) k+z) := div_nonneg hz (add_nonneg hn.le hz)
  rw [heq,norm_mul,norm_neg,norm_mul,norm_mul,
    Real.norm_of_nonneg hg0,Real.norm_of_nonneg (cutoff_bounds hR hθ n hk).1]
  exact (mul_le_mul (mul_le_mul_of_nonneg_right hf (norm_nonneg _)) hgap hg0
    (mul_nonneg (norm_nonneg F) (norm_nonneg _))).trans_eq (by ring)

theorem actual_shiftedDivide_continuousAt_zero {R : ℝ} (hR : 0<R) {θ : Parameter}
    (hθ : θ∈positiveDomain R) :
    Tendsto (fun z : Set.Ici (0:ℝ)=>shiftedDivide hR hθ z.property)
      (𝓝 ⟨0,show (0:ℝ)≤0 from le_rfl⟩) (𝓝 (divide hR hθ)) := by
  apply (tendsto_iff_norm_sub_tendsto_zero
    (E := Lp ℝ ∞ (cubeVolume R)→L[ℝ]Space R)).mpr
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨n,hn⟩ := ((errorVector_norm_tendsto hR hθ).eventually (gt_mem_nhds hε)).exists
  have he : ∀ᶠz : Set.Ici (0:ℝ) in 𝓝 ⟨0,show (0:ℝ)≤0 from le_rfl⟩,(z:ℝ)<scale n :=
    (continuous_subtype_val.tendsto (⟨0,show (0:ℝ)≤0 from le_rfl⟩ : Set.Ici (0:ℝ))).eventually
      (gt_mem_nhds (scale_pos n))
  filter_upwards [he] with z hz
  rw [Real.dist_eq,sub_zero,abs_of_nonneg (norm_nonneg _)]
  exact (shiftedDivide_error_bound hR hθ n z.property hz.le).trans_lt hn

end
end Resonance.ShiftedDivideLimit
