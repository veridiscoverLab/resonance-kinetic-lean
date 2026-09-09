import Resonance.LocalizedDerivativeCoefficients
import Resonance.ContinuousCollisionPerturbation

/-! Actual C(D) derivative coefficients on the original sharp quartet.
Only the bulk amplitude is small; corner values remain merely bounded.
The full diagonal is retained separately, never estimated by the small
marked off-diagonal kernel. -/
open Set MeasureTheory
open scoped ENNReal
namespace Resonance.ActualLocalizedOffDiagonal
noncomputable section
open ResonantMeasure FreeTransport FiberContinuity
open FrequencyWeightedForm JointWeightComparison
open ContinuousWeightedEnergy (toWeighted)
open ContinuousCollisionPerturbation CornerPairTruncation
open LocalizedDerivativeCoefficients QuartetCoefficientLocalization AllMarkedQuartetReaders
set_option maxHeartbeats 2200000

def coefficientAt (R : ℝ) (f N : CubeFunction R) (i j : Fin 4) (q : FourMomenta) : ℝ:=
  relativeCoefficient (fun l=>continuousExtension R f (q l))
    (fun l=>continuousExtension R N (q l)) i j

theorem coefficientAt_measurable (R : ℝ) (f N : CubeFunction R) (i j : Fin 4) :
    Measurable (coefficientAt R f N i j) :=
  relativeCoefficient_measurable _ _
    (fun l=>(continuousExtension R f).continuous.measurable.comp (measurable_pi_apply l))
    (fun l=>(continuousExtension R N).continuous.measurable.comp (measurable_pi_apply l)) i j

theorem actual_local_difference (R : ℝ) (f N : CubeFunction R) {M κ η : ℝ}
    (_hM : 0≤M) (hκ : 0≤κ) (hf : ∀k,|f k|≤M) (hN : ∀k,|N k|≤M)
    (hbulk : ∀k:MomentumDomain R, η<CornerFrequencyBounds.cornerDepth R k → |f k-N k|≤κ)
    (k : MomentumDomain R) :
    |f k-N k|≤κ+2*M*cut R η k := by
  by_cases hk : (k:E)∈CornerNewtonTail.fullTail R η
  · have hc : cut R η k=1:=by simp [cut,hk]
    rw [hc,mul_one]
    have ha:=abs_sub (f k) (N k)
    linarith [hf k,hN k]
  · have hd : η<CornerFrequencyBounds.cornerDepth R k := by
      exact lt_of_not_ge (fun hd=>hk ⟨k.property,hd⟩)
    simpa [cut,hk] using hbulk k hd

theorem actual_coefficient_envelope {R : ℝ} (_hR : 0<R) (f N : CubeFunction R)
    {m M κ η : ℝ} (hm : 0 < m) (hM : 0≤M) (hκ : 0≤κ)
    (hf : ∀k,|f k|≤M) (hN : ∀k,m≤N k ∧ |N k|≤M)
    (hbulk : ∀k:MomentumDomain R, η<CornerFrequencyBounds.cornerDepth R k → |f k-N k|≤κ)
    (i j : Fin 4) :
    ∀ᵐq∂WeightedJointMeasure.jointMeasure R unitParameter,
      |coefficientAt R f N i j q|≤envelope R ((6*M^2/m)*κ) (12*M^3/m) η q := by
  rw [unit_joint R]
  filter_upwards [ae_iff.mpr (pairing_supported_on_fullResonance R)] with q hq
  have he (l:Fin 4) : |continuousExtension R f (q l)-continuousExtension R N (q l)|
      ≤κ+2*M*cut R η (q l) := by
    rw [continuousExtension_eq R f ⟨q l,hq.1 l⟩,continuousExtension_eq R N ⟨q l,hq.1 l⟩]
    exact actual_local_difference R f N hM hκ hf (fun k=>(hN k).2) hbulk ⟨q l,hq.1 l⟩
  apply relativeCoefficient_marked_bound _ _ _ hm hM hκ (fun l=>(cut_bounds R η (q l)).1)
  · intro l
    rw [continuousExtension_eq R f ⟨q l,hq.1 l⟩]
    exact hf _
  · intro l
    rw [continuousExtension_eq R N ⟨q l,hq.1 l⟩]
    exact hN _
  · exact he

def energyCost (R m M κ η : ℝ) : ℝ:=
  (6*M^2/m)*κ+4*(12*M^3/m)*markedOmega R unitParameter η

theorem energyCost_nonnegative (R η : ℝ) {m M κ : ℝ}
    (hm : 0 < m) (hM : 0≤M) (hκ : 0≤κ) : 0≤energyCost R m M κ η := by
  unfold energyCost
  have hw:=markedOmega_nonnegative R unitParameter η
  positivity

def pairDensity (R : ℝ) (f N u : CubeFunction R) (i j : Fin 4) (q : FourMomenta) : ℝ:=
  coefficientAt R f N i j q*continuousExtension R u (q i)*continuousExtension R u (q j)

/-- Every one of the twelve ordered cross pairs is estimated on the
original Ξ, with all free coefficient legs retained and with the actual
fixed-reference Hν norm on the right. -/
theorem actual_offdiagonal_pair_bound {R : ℝ} (hR : 0<R) (f N u : CubeFunction R)
    {m M κ η : ℝ} (hm : 0 < m) (hM : 0≤M) (hκ : 0≤κ)
    (hf : ∀k,|f k|≤M) (hN : ∀k,m≤N k ∧ |N k|≤M)
    (hbulk : ∀k:MomentumDomain R, η<CornerFrequencyBounds.cornerDepth R k → |f k-N k|≤κ)
    (i j : Fin 4) (hij : i≠j) :
    Integrable (pairDensity R f N u i j) (pairingMeasure R) ∧
    |∫q,pairDensity R f N u i j q∂pairingMeasure R|≤
      (energyCost R m M κ η*‖toUnit hR‖^2)*‖toWeighted hR u‖^2 := by
  let v:=toUnit hR (toWeighted hR u)
  have ha : AEStronglyMeasurable (coefficientAt R f N i j)
      (WeightedJointMeasure.jointMeasure R unitParameter):=
    (coefficientAt_measurable R f N i j).aestronglyMeasurable
  have hb:=actual_coefficient_envelope hR f N hm hM hκ hf hN hbulk i j
  have hread:=actual_signed_coefficient_bound hR (unitParameter_positive R) j i hij.symm
    (by positivity : 0≤(6*M^2/m)*κ) (by positivity : 0≤12*M^3/m) η v v ha hb
  have he : (fun q=>coefficientAt R f N i j q*v (q i)*v (q j))=ᵐ[
      WeightedJointMeasure.jointMeasure R unitParameter] pairDensity R f N u i j := by
    filter_upwards [(all_legs_preserve R unitParameter i).quasiMeasurePreserving.ae_eq (toUnit_ae hR u),
      (all_legs_preserve R unitParameter j).quasiMeasurePreserving.ae_eq (toUnit_ae hR u)] with q hi hj
    simp only [Function.comp_def] at hi hj
    rw [show v (q i)=continuousExtension R u (q i) from hi,
      show v (q j)=continuousExtension R u (q j) from hj]
    rfl
  have hInt:=hread.1.congr he
  have hbound : |∫q,pairDensity R f N u i j q∂WeightedJointMeasure.jointMeasure R unitParameter|
      ≤energyCost R m M κ η*‖v‖*‖v‖ := by
    rw [←integral_congr_ae he]
    exact hread.2
  rw [unit_joint R] at hInt hbound
  refine ⟨hInt,?_⟩
  have hv: ‖v‖^2≤‖toUnit hR‖^2*‖toWeighted hR u‖^2 := by
    have hp:=mul_self_le_mul_self (norm_nonneg v) ((toUnit hR).le_opNorm (toWeighted hR u))
    nlinarith [hp]
  calc
    _≤energyCost R m M κ η*‖v‖^2:=by simpa only [pow_two,mul_assoc] using hbound
    _≤energyCost R m M κ η*(‖toUnit hR‖^2*‖toWeighted hR u‖^2):=
      mul_le_mul_of_nonneg_left hv (energyCost_nonnegative R η hm hM hκ)
    _=_:=by ring

end
end Resonance.ActualLocalizedOffDiagonal
