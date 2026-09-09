import Resonance.DominatedPairKernelConvergence
import Resonance.CornerPairTruncation
import Mathlib.MeasureTheory.Measure.Decomposition.IntegralRNDeriv

/-! A corner mark on any actual quartet leg, including an unobserved
leg, is retained before pushing the same joint measure to a pair. Its
normalized kernel is a genuine Radon--Nikodym derivative of this pushforward. -/
open Set MeasureTheory Filter
open scoped ENNReal Topology
namespace Resonance.MarkedQuartetPairKernel
noncomputable section
open ResonantMeasure WeightedJointMeasure FrequencyWeightedForm
open CornerPairTruncation SpatialMomentumSections ActualPairKernels
set_option maxHeartbeats 1800000

def pairLeg (b : Bool) : Fin 4:=if b then 1 else 2
def pairRead (b : Bool) (q : FourMomenta) : E×E:=(q 0,q (pairLeg b))

theorem pairRead_measurable (b : Bool) : Measurable (pairRead b) :=
  (measurable_pi_apply 0).prodMk (measurable_pi_apply (pairLeg b))

def markedSet (R : ℝ) (l : Fin 4) (η : ℝ) : Set FourMomenta :=
  (fun q=>q l) ⁻¹' CornerNewtonTail.fullTail R η

theorem markedSet_measurable (R : ℝ) (l : Fin 4) (η : ℝ) : MeasurableSet (markedSet R l η) :=
  (CornerNewtonTail.fullTail_measurable R η).preimage (measurable_pi_apply l)

def markedJoint (R : ℝ) (θ : Thermodynamics.Parameter) (l : Fin 4) (η : ℝ) : Measure FourMomenta :=
  (jointMeasure R θ).restrict (markedSet R l η)

def markedPair (R : ℝ) (θ : Thermodynamics.Parameter) (b : Bool) (l : Fin 4) (η : ℝ) : Measure (E×E) :=
  (markedJoint R θ l η).map (pairRead b)

def pairBase (R : ℝ) (θ : Thermodynamics.Parameter) : Measure (E×E):=
  (marginal R θ).prod (marginal R θ)

def markedKernel (R : ℝ) (θ : Thermodynamics.Parameter) (b : Bool) (l : Fin 4) (η : ℝ)
    (p : E×E) : ℝ:=((markedPair R θ b l η).rnDeriv (pairBase R θ) p).toReal

theorem markedKernel_measurable (R : ℝ) (θ : Thermodynamics.Parameter)
    (b : Bool) (l : Fin 4) (η : ℝ) : Measurable (markedKernel R θ b l η) :=
  (Measure.measurable_rnDeriv _ _).ennreal_toReal

theorem markedKernel_nonnegative (R : ℝ) (θ : Thermodynamics.Parameter)
    (b : Bool) (l : Fin 4) (η : ℝ) (p : E×E) : 0 ≤ markedKernel R θ b l η p :=
  ENNReal.toReal_nonneg

theorem markedPair_finite {R : ℝ} (hR : 0 ≤ R) {θ : Thermodynamics.Parameter}
    (hθ : θ∈Thermodynamics.positiveDomain R) (b : Bool) (l : Fin 4) (η : ℝ) :
    IsFiniteMeasure (markedPair R θ b l η) := by
  letI:=jointMeasure_finite hR hθ
  unfold markedPair markedJoint
  infer_instance

theorem pairBase_finite {R : ℝ} (hR : 0 ≤ R) {θ : Thermodynamics.Parameter}
    (hθ : θ∈Thermodynamics.positiveDomain R) : IsFiniteMeasure (pairBase R θ) := by
  letI:=actual_marginal_finite hR hθ
  unfold pairBase
  infer_instance

theorem actual_pair_normalized {R : ℝ} (hR : 0 < R) {θ : Thermodynamics.Parameter}
    (hθ : θ∈Thermodynamics.positiveDomain R) (b : Bool) :
    (jointMeasure R θ).map (pairRead b)=
      (pairBase R θ).withDensity (fun p=>ENNReal.ofReal (pairKernel R θ b p)) := by
  cases b
  · exact cross_pair_normalized hR hθ
  · exact incoming_pair_normalized hR hθ

theorem pairKernel_measurable (R : ℝ) (θ : Thermodynamics.Parameter) (b : Bool) :
    Measurable (pairKernel R θ b) := by
  cases b
  · exact NormalizedPairDensity.realKernel_measurable
      (ActualPairNormalization.marginalDensity_measurable R θ)
      (ActualPairNormalization.marginalDensity_measurable R θ)
      (CrossPairDensity.density_measurable R (weight_measurable θ))
  · exact NormalizedPairDensity.realKernel_measurable
      (ActualPairNormalization.marginalDensity_measurable R θ)
      (ActualPairNormalization.marginalDensity_measurable R θ)
      (IncomingPairDensity.density_measurable R (weight_measurable θ))

theorem pairKernel_nonnegative (R : ℝ) (θ : Thermodynamics.Parameter) (b : Bool) (p : E×E) :
    0 ≤ pairKernel R θ b p := by
  cases b <;> exact ENNReal.toReal_nonneg

theorem markedPair_le {R : ℝ} (hR : 0 < R) {θ : Thermodynamics.Parameter}
    (hθ : θ∈Thermodynamics.positiveDomain R) (b : Bool) (l : Fin 4) (η : ℝ) :
    markedPair R θ b l η ≤
      (pairBase R θ).withDensity (fun p=>ENNReal.ofReal (pairKernel R θ b p)) := by
  rw [←actual_pair_normalized hR hθ b]
  exact Measure.map_mono Measure.restrict_le_self (pairRead_measurable b)

theorem markedPair_ac {R : ℝ} (hR : 0 < R) {θ : Thermodynamics.Parameter}
    (hθ : θ∈Thermodynamics.positiveDomain R) (b : Bool) (l : Fin 4) (η : ℝ) :
    markedPair R θ b l η ≪ pairBase R θ :=
  (markedPair_le hR hθ b l η).absolutelyContinuous.trans (withDensity_absolutelyContinuous _ _)

/-- The free-leg mark produces an actual subkernel of the full pair law. -/
theorem markedKernel_dominated {R : ℝ} (hR : 0 < R) {θ : Thermodynamics.Parameter}
    (hθ : θ∈Thermodynamics.positiveDomain R) (b : Bool) (l : Fin 4) (η : ℝ) :
    ∀ᵐp∂pairBase R θ,0 ≤ markedKernel R θ b l η p ∧
      markedKernel R θ b l η p ≤ pairKernel R θ b p := by
  letI:=pairBase_finite hR.le hθ
  have hr : (markedPair R θ b l η).rnDeriv (pairBase R θ) ≤ᵐ[pairBase R θ]
      (fun p=>ENNReal.ofReal (pairKernel R θ b p)) := by
    apply ae_le_of_forall_setLIntegral_le_of_sigmaFinite (Measure.measurable_rnDeriv _ _)
    intro s hs _
    apply (Measure.setLIntegral_rnDeriv_le s).trans
    have hb:=markedPair_le hR hθ b l η s
    rwa [withDensity_apply _ hs] at hb
  filter_upwards [hr] with p hp
  refine ⟨ENNReal.toReal_nonneg,?_⟩
  have hb:=ENNReal.toReal_mono ENNReal.ofReal_ne_top hp
  simpa only [ENNReal.toReal_ofReal (pairKernel_nonnegative R θ b p)] using hb

theorem markedKernel_memLp {R : ℝ} (hR : 0 < R) {θ : Thermodynamics.Parameter}
    (hθ : θ∈Thermodynamics.positiveDomain R) (b : Bool) (l : Fin 4) (η : ℝ) :
    MemLp (markedKernel R θ b l η) 2 (pairBase R θ) :=
  DominatedPairKernelConvergence.dominated_memLp (pairKernel_memLp hR hθ b)
    (markedKernel_measurable R θ b l η).aestronglyMeasurable (markedKernel_dominated hR hθ b l η)

/-- This identifies the density with the marked original pushforward,
not merely with a kernel having the desired upper bound. -/
theorem markedKernel_measure {R : ℝ} (hR : 0 < R) {θ : Thermodynamics.Parameter}
    (hθ : θ∈Thermodynamics.positiveDomain R) (b : Bool) (l : Fin 4) (η : ℝ) :
    (pairBase R θ).withDensity (fun p=>ENNReal.ofReal (markedKernel R θ b l η p))=
      markedPair R θ b l η := by
  letI:=markedPair_finite hR.le hθ b l η
  letI:=pairBase_finite hR.le hθ
  calc
    _=(pairBase R θ).withDensity ((markedPair R θ b l η).rnDeriv (pairBase R θ)) := by
      apply withDensity_congr_ae
      filter_upwards [Measure.rnDeriv_lt_top (markedPair R θ b l η) (pairBase R θ)] with p hp
      exact ENNReal.ofReal_toReal hp.ne
    _=markedPair R θ b l η:=Measure.withDensity_rnDeriv_eq _ _ (markedPair_ac hR hθ b l η)

theorem markedKernel_mass {R : ℝ} (hR : 0 < R) {θ : Thermodynamics.Parameter}
    (hθ : θ∈Thermodynamics.positiveDomain R) (b : Bool) (l : Fin 4) (η : ℝ) :
    (∫p,markedKernel R θ b l η p∂pairBase R θ)=
      ∫q,cut R η (q l)∂jointMeasure R θ := by
  letI:=markedPair_finite hR.le hθ b l η
  letI:=pairBase_finite hR.le hθ
  unfold markedKernel
  rw [Measure.integral_toReal_rnDeriv (markedPair_ac hR hθ b l η)]
  have he : (fun q:FourMomenta=>cut R η (q l))=
      (markedSet R l η).indicator (fun _=>1) := rfl
  rw [he,integral_indicator (markedSet_measurable R l η),integral_const]
  simp only [measureReal_def,markedPair,Measure.map_apply (pairRead_measurable b) MeasurableSet.univ,
    preimage_univ,markedJoint,Measure.restrict_apply_univ,smul_eq_mul,mul_one]

theorem actual_marked_mass_tendsto {R : ℝ} (hR : 0 < R) {θ : Thermodynamics.Parameter}
    (hθ : θ∈Thermodynamics.positiveDomain R) (l : Fin 4) :
    Tendsto (fun η:ℝ=>∫q,cut R η (q l)∂jointMeasure R θ) (𝓝 0) (𝓝 0) := by
  letI:=jointMeasure_finite hR.le hθ
  have ht:=tendsto_integral_filter_of_dominated_convergence
    (μ:=jointMeasure R θ) (l:=𝓝 (0:ℝ)) (F:=fun η q=>cut R η (q l))
    (f:=fun _=>0) (fun _=>1)
  simp only [integral_zero] at ht
  apply ht
  · exact Eventually.of_forall (fun η=>((cut_measurable R η).comp
      (measurable_pi_apply l)).aestronglyMeasurable)
  · exact Eventually.of_forall (fun η=>ae_of_all _ (fun q=>by
      simpa only [Real.norm_eq_abs] using (cut_bounds R η (q l)).2))
  · exact integrable_const 1
  · filter_upwards [(all_legs_preserve R θ l).quasiMeasurePreserving.ae
      (depth_positive_marginal hR θ)] with q hq
    exact cut_tendsto hq

/-- The mark may be at either fixed leg or either free leg. Its actual
normalized kernel vanishes in L² of the one common product marginal. -/
theorem actual_marked_kernel_L2_tendsto {R : ℝ} (hR : 0 < R) {θ : Thermodynamics.Parameter}
    (hθ : θ∈Thermodynamics.positiveDomain R) (b : Bool) (l : Fin 4) :
    Tendsto (fun η:ℝ=>eLpNorm (markedKernel R θ b l η) 2 (pairBase R θ))
      (𝓝 0) (𝓝 0) := by
  letI:=pairBase_finite hR.le hθ
  apply DominatedPairKernelConvergence.actual_mass_to_L2 (μ:=pairBase R θ)
    (show MemLp (pairKernel R θ b) 2 (pairBase R θ) from pairKernel_memLp hR hθ b)
    (fun η=>(markedKernel_measurable R θ b l η).aestronglyMeasurable)
    (fun η=>markedKernel_dominated hR hθ b l η)
  simp_rw [markedKernel_mass hR hθ b l]
  exact actual_marked_mass_tendsto hR hθ l

end
end Resonance.MarkedQuartetPairKernel
