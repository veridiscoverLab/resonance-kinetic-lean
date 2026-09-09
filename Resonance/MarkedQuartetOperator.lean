import Resonance.MarkedQuartetPairKernel
import Resonance.L2KernelPairing

/-! Actual corner-marked off-diagonal readers. The marker remains on the
same original quartet before either observed leg is read. -/
open Set MeasureTheory Filter
open scoped ENNReal Topology
namespace Resonance.MarkedQuartetOperator
noncomputable section
open ResonantMeasure WeightedJointMeasure FrequencyWeightedForm
open CornerPairTruncation MarkedQuartetPairKernel LpOperators
set_option maxHeartbeats 1800000

theorem jointCut_memLp (R : ℝ) (θ : Thermodynamics.Parameter) (l : Fin 4) (η : ℝ) :
    MemLp (fun q:FourMomenta=>cut R η (q l)) ∞ (jointMeasure R θ) := by
  apply memLp_top_of_bound ((cut_measurable R η).comp (measurable_pi_apply l)).aestronglyMeasurable 1
  exact ae_of_all _ (fun q=>by simpa only [Real.norm_eq_abs] using (cut_bounds R η (q l)).2)

def jointCut (R : ℝ) (θ : Thermodynamics.Parameter) (l : Fin 4) (η : ℝ) : J R θ→L[ℝ]J R θ :=
  multiplyCLM (jointCut_memLp R θ l η)

def markedOperator (R : ℝ) (θ : Thermodynamics.Parameter) (i j l : Fin 4) (η : ℝ) :
    H R θ→L[ℝ]H R θ :=
  (pullback R θ i).toContinuousLinearMap.adjoint.comp
    ((jointCut R θ l η).comp (pullback R θ j).toContinuousLinearMap)

theorem actual_marked_pairing (R : ℝ) (θ : Thermodynamics.Parameter) (i j l : Fin 4)
    (η : ℝ) (u v : H R θ) :
    inner ℝ v (markedOperator R θ i j l η u)=
      ∫q,cut R η (q l)*u (q j)*v (q i)∂jointMeasure R θ := by
  rw [show inner ℝ v (markedOperator R θ i j l η u)=
    inner ℝ (pullback R θ i v) (jointCut R θ l η (pullback R θ j u)) from
    ContinuousLinearMap.adjoint_inner_right (pullback R θ i).toContinuousLinearMap v _]
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [multiply_ae (jointCut_memLp R θ l η) (pullback R θ j u),
    pullback_ae R θ i v,pullback_ae R θ j u] with q hm hv hu
  change (jointCut R θ l η (pullback R θ j u)) q*(pullback R θ i v) q=_
  rw [show (jointCut R θ l η (pullback R θ j u)) q=
    (pullback R θ j u) q*cut R η (q l) from hm,hv,hu]
  ring

theorem actual_marked_integrable (R : ℝ) (θ : Thermodynamics.Parameter) (i j l : Fin 4)
    (η : ℝ) (u v : H R θ) :
    Integrable (fun q=>cut R η (q l)*u (q j)*v (q i)) (jointMeasure R θ) := by
  apply ((Lp.memLp (jointCut R θ l η (pullback R θ j u))).integrable_mul
    (Lp.memLp (pullback R θ i v))).congr
  filter_upwards [multiply_ae (jointCut_memLp R θ l η) (pullback R θ j u),
    pullback_ae R θ i v,pullback_ae R θ j u] with q hm hv hu
  change (jointCut R θ l η (pullback R θ j u)) q*(pullback R θ i v) q=_
  rw [show (jointCut R θ l η (pullback R θ j u)) q=
    (pullback R θ j u) q*cut R η (q l) from hm,hv,hu]
  ring

theorem marked_pair_integral (R : ℝ) (θ : Thermodynamics.Parameter) (b : Bool) (l : Fin 4)
    (η : ℝ) (u v : H R θ) :
    inner ℝ v (markedOperator R θ 0 (pairLeg b) l η u)=
      ∫p,u p.2*v p.1∂markedPair R θ b l η := by
  have hm : Measurable (fun p:E×E=>u p.2*v p.1) :=
    ((Lp.stronglyMeasurable u).measurable.comp measurable_snd).mul
      ((Lp.stronglyMeasurable v).measurable.comp measurable_fst)
  rw [actual_marked_pairing,markedPair,integral_map (pairRead_measurable b).aemeasurable
    hm.aestronglyMeasurable]
  unfold markedJoint
  rw [←integral_indicator (markedSet_measurable R l η)]
  congr 1
  ext q
  by_cases h:q∈markedSet R l η
  · simp [markedSet,cut,show q l∈CornerNewtonTail.fullTail R η from h,pairRead]
  · simp [markedSet,cut,show q l∉CornerNewtonTail.fullTail R η from h]

theorem actual_marked_kernel_pairing {R : ℝ} (hR : 0<R) {θ : Thermodynamics.Parameter}
    (hθ : θ∈Thermodynamics.positiveDomain R) (b : Bool) (l : Fin 4) (η : ℝ) (u v : H R θ) :
    inner ℝ v (markedOperator R θ 0 (pairLeg b) l η u)=
      ∫p,markedKernel R θ b l η p*u p.2*v p.1∂pairBase R θ := by
  rw [marked_pair_integral,←markedKernel_measure hR hθ b l η,
    integral_withDensity_eq_integral_toReal_smul
      (markedKernel_measurable R θ b l η).ennreal_ofReal
      (ae_of_all _ (fun _=>ENNReal.ofReal_lt_top))]
  apply integral_congr_ae
  apply ae_of_all
  intro p
  dsimp only
  rw [ENNReal.toReal_ofReal (markedKernel_nonnegative R θ b l η p),smul_eq_mul]
  exact (mul_assoc _ _ _).symm

def markedCost (R : ℝ) (θ : Thermodynamics.Parameter) (b : Bool) (l : Fin 4) (η : ℝ) : ℝ:=
  (eLpNorm (markedKernel R θ b l η) 2 (pairBase R θ)).toReal

theorem markedCost_nonnegative (R : ℝ) (θ : Thermodynamics.Parameter)
    (b : Bool) (l : Fin 4) (η : ℝ) : 0 ≤ markedCost R θ b l η := ENNReal.toReal_nonneg

theorem actual_marked_norm_bound {R : ℝ} (hR : 0<R) {θ : Thermodynamics.Parameter}
    (hθ : θ∈Thermodynamics.positiveDomain R) (b : Bool) (l : Fin 4) (η : ℝ) :
    ‖markedOperator R θ 0 (pairLeg b) l η‖ ≤ markedCost R θ b l η := by
  letI:=SpatialMomentumSections.actual_marginal_finite hR.le hθ
  let K := (markedKernel_memLp hR hθ b l η).toLp (markedKernel R θ b l η)
  have hr : L2KernelPairing.Represents (marginal R θ) (marginal R θ) K
      (markedOperator R θ 0 (pairLeg b) l η) := by
    intro u v
    rw [actual_marked_kernel_pairing hR hθ]
    apply integral_congr_ae
    filter_upwards [MemLp.coeFn_toLp (markedKernel_memLp hR hθ b l η)] with p hp
    exact congrArg (fun z=>z*u p.2*v p.1) hp.symm
  have hb:=L2KernelPairing.represents_norm_bound (marginal R θ) (marginal R θ) hr
  exact hb.trans_eq (Lp.norm_toLp (markedKernel R θ b l η) (markedKernel_memLp hR hθ b l η))

theorem actual_marked_cost_tendsto {R : ℝ} (hR : 0<R) {θ : Thermodynamics.Parameter}
    (hθ : θ∈Thermodynamics.positiveDomain R) (b : Bool) (l : Fin 4) :
    Tendsto (markedCost R θ b l) (𝓝 0) (𝓝 0) := by
  have h:=ENNReal.continuousAt_toReal (by simp : (0:ℝ≥0∞)≠∞)
  simpa only [ENNReal.toReal_zero,markedCost] using
    h.tendsto.comp (actual_marked_kernel_L2_tendsto hR hθ b l)

end
end Resonance.MarkedQuartetOperator
