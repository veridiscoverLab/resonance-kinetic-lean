import Resonance.JointWeightComparison

/-! Changing the positive quartet weight transports the same function
and the same complete difference.  No independent representatives are
chosen for different collision legs. -/
open MeasureTheory
open scoped ENNReal
namespace Resonance.FullDifferenceTransport
noncomputable section
open ResonantMeasure WeightedJointMeasure FrequencyWeightedForm LpOperators
open JointWeightComparison

theorem changeMeasure_inverse {X : Type*} [MeasurableSpace X]
    {μ ν : Measure X} {C D : ℝ≥0∞} (hC : C≠∞) (hD : D≠∞)
    (hμν : μ≤C • ν) (hνμ : ν≤D • μ) (f : Lp ℝ 2 μ) :
    changeMeasure hC hμν (changeMeasure hD hνμ f)=f := by
  apply Lp.ext
  have hac : μ≪ν := Measure.absolutelyContinuous_of_le_smul hμν
  filter_upwards [changeMeasure_ae hC hμν (changeMeasure hD hνμ f),
    hac.ae_eq (changeMeasure_ae hD hνμ f)] with x h1 h2
  exact h1.trans h2

theorem actual_fullDifference_change {R : ℝ} {θ β : Thermodynamics.Parameter}
    {C : ℝ≥0∞} (hC : C≠∞) (hc : jointMeasure R θ≤C • jointMeasure R β)
    (f : H R β) :
    fullDifference R θ (changeMeasure hC (marginal_of_joint_comparison hc) f)=
      changeMeasure hC hc (fullDifference R β f) := by
  let h := changeMeasure hC (marginal_of_joint_comparison hc) f
  have hh : (h : E→ℝ)=ᵐ[marginal R θ] f :=
    changeMeasure_ae hC (marginal_of_joint_comparison hc) f
  have hac : jointMeasure R θ≪jointMeasure R β :=
    Measure.absolutelyContinuous_of_le_smul hc
  apply Lp.ext
  filter_upwards [fullDifference_ae R θ h,
    changeMeasure_ae hC hc (fullDifference R β f),
    hac.ae_eq (fullDifference_ae R β f),
    (all_legs_preserve R θ 0).quasiMeasurePreserving.ae_eq hh,
    (all_legs_preserve R θ 1).quasiMeasurePreserving.ae_eq hh,
    (all_legs_preserve R θ 2).quasiMeasurePreserving.ae_eq hh,
    (all_legs_preserve R θ 3).quasiMeasurePreserving.ae_eq hh]
    with q hq hchange hf h0 h1 h2 h3
  rw [hq,hchange,hf]
  simp only [Function.comp_def] at h0 h1 h2 h3
  simp only [CollisionForm.rawDifference,h0,h1,h2,h3]

theorem actual_kernel_change {R : ℝ} {θ β : Thermodynamics.Parameter}
    {C : ℝ≥0∞} (hC : C≠∞) (hc : jointMeasure R θ≤C • jointMeasure R β)
    {f : H R β} (hf : f∈(fullDifference R β).ker) :
    changeMeasure hC (marginal_of_joint_comparison hc) f∈(fullDifference R θ).ker := by
  change fullDifference R θ _=0
  have hz : fullDifference R β f=0 := hf
  rw [actual_fullDifference_change hC hc,hz]
  exact (changeCLM hC hc).map_zero

end
end Resonance.FullDifferenceTransport
