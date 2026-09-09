import Resonance.PositiveLossShift
import Resonance.MonotoneRowVanishing

/-! Original incoming and crossed reference rows lose the small-frequency
cutoff uniformly at every closed-cube output, by actual row continuity.
This is the z-down-to-zero input required for the original resolvent. -/
open MeasureTheory Set Filter
open scoped ENNReal Topology
namespace Resonance.ShiftRowVanishing
noncomputable section
set_option maxHeartbeats 1200000
open ResonantMeasure Thermodynamics WeightedJointMeasure CollisionFrequency
open ActualPairNormalization ActualReferenceRowOperator JointWeightComparison

def scale (n : ℕ) : ℝ := 1/((n:ℝ)+1)

theorem scale_pos (n : ℕ) : 0<scale n := by unfold scale; positivity

theorem scale_antitone : Antitone scale := by
  intro n m hnm
  unfold scale
  rw [one_div,one_div]
  exact inv_anti₀ (by positivity) (by exact_mod_cast Nat.add_le_add_right hnm 1)

theorem scale_tendsto : Tendsto scale atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat

def cutoff (R : ℝ) (θ : Parameter) (n : ℕ) (k : E) : ℝ :=
  scale n/(lossFrequency R (profile θ) k+scale n)

theorem cutoff_measurable (R : ℝ) (θ : Parameter) (n : ℕ) : Measurable (cutoff R θ n) :=
  measurable_const.div ((CollisionMarginalDensity.lossFrequency_measurable R (profile_measurable θ)).add_const _)

theorem cutoff_bounds {R : ℝ} (hR : 0<R) {θ : Parameter} (hθ : θ∈positiveDomain R)
    (n : ℕ) {k : E} (hk : k∈cube R) : 0≤cutoff R θ n k ∧ cutoff R θ n k≤1 := by
  have hn := ActualFrequencyRatio.loss_nonnegative hR hθ hk
  have hz := scale_pos n
  unfold cutoff
  exact ⟨div_nonneg hz.le (add_nonneg hn hz.le),
    (div_le_one (add_pos_of_nonneg_of_pos hn hz)).mpr (le_add_of_nonneg_left hn)⟩

theorem cutoff_antitone {R : ℝ} (hR : 0<R) {θ : Parameter} (hθ : θ∈positiveDomain R)
    {k : E} (hk : k∈cube R) : Antitone (fun n=>cutoff R θ n k) := by
  intro n m hnm
  have hn := ActualFrequencyRatio.loss_nonnegative hR hθ hk
  have hz := scale_antitone hnm
  unfold cutoff
  apply (div_le_div_iff₀ (add_pos_of_nonneg_of_pos hn (scale_pos m))
    (add_pos_of_nonneg_of_pos hn (scale_pos n))).mpr
  nlinarith

theorem cutoff_tendsto {R : ℝ} (hR : 0<R) {θ : Parameter} (hθ : θ∈positiveDomain R) :
    ∀ᵐk∂cubeVolume R,Tendsto (fun n=>cutoff R θ n k) atTop (𝓝 0) := by
  filter_upwards [LinftyPhysicalDomain.loss_positive_ae hR hθ] with k hk
  have ht := scale_tendsto.div ((tendsto_const_nhds (x:=lossFrequency R (profile θ) k)).add scale_tendsto)
    (by simpa only [add_zero] using hk.ne')
  simpa only [zero_div,add_zero] using ht

theorem incoming_cutoff_vanishes {R : ℝ} (hR : 0<R) {θ : Parameter} (hθ : θ∈positiveDomain R) :
    TendstoUniformly (fun n (k : cube R)=>∫p,incomingRow R unitParameter k p*cutoff R θ n p∂cubeMeasure R)
      (fun _=>0) atTop := by
  apply MonotoneRowVanishing.uniform_row_vanishing (incomingRow R unitParameter)
    (incomingRow_integrable hR (unitParameter_positive R))
    (incomingRow_L1_continuous hR (unitParameter_positive R))
  · intro k
    exact ae_of_all _ (fun p=>mul_nonneg
      (CrossRowWeightedBounds.inverseFrequency_nonnegative R p) ENNReal.toReal_nonneg)
  · intro n
    exact ((cutoff_measurable R θ n).comp measurable_subtype_coe).aestronglyMeasurable
  · intro n
    exact ae_of_all _ (fun p=>cutoff_bounds hR hθ n p.property)
  · intro n m hnm
    exact ae_of_all _ (fun p=>cutoff_antitone hR hθ p.property hnm)
  · exact (CubeLinftyCoordinates.val_preserves R).quasiMeasurePreserving.ae (cutoff_tendsto hR hθ)

theorem cross_cutoff_vanishes {R : ℝ} (hR : 0<R) {θ : Parameter} (hθ : θ∈positiveDomain R) :
    TendstoUniformly (fun n (k : cube R)=>∫p,crossRow R unitParameter k p*cutoff R θ n p∂cubeMeasure R)
      (fun _=>0) atTop := by
  apply MonotoneRowVanishing.uniform_row_vanishing (crossRow R unitParameter)
    (crossRow_integrable hR (unitParameter_positive R))
    (crossRow_L1_continuous hR (unitParameter_positive R))
  · intro k
    exact ae_of_all _ (fun p=>mul_nonneg
      (CrossRowWeightedBounds.inverseFrequency_nonnegative R p) ENNReal.toReal_nonneg)
  · intro n
    exact ((cutoff_measurable R θ n).comp measurable_subtype_coe).aestronglyMeasurable
  · intro n
    exact ae_of_all _ (fun p=>cutoff_bounds hR hθ n p.property)
  · intro n m hnm
    exact ae_of_all _ (fun p=>cutoff_antitone hR hθ p.property hnm)
  · exact (CubeLinftyCoordinates.val_preserves R).quasiMeasurePreserving.ae (cutoff_tendsto hR hθ)

end
end Resonance.ShiftRowVanishing
