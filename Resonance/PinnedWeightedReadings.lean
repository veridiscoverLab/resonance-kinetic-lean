import Resonance.PinnedQuarterSymmetrization
import Resonance.PinnedWeakIntegrability

/-! The positive four-leg measure and the explicitly weighted original
coarea integral agree exactly. This is also the normalization dictionary
between the maximal form and the full signed current. -/
open Set MeasureTheory Filter
open scoped ContDiff
namespace Resonance.PinnedWeightedReadings
noncomputable section
open PinnedPeriodicity PinnedMeasureNormalization PinnedMaximalDifference
open PinnedSmoothDomain PinnedQuarterSymmetrization PinnedTorusPermutations

theorem weighted_integral {d : ℝ} {a : FourCircle→ℝ} (ha : Continuous a)
    (ha0 : ∀q,0≤a q) (f : CircleMomenta→ℂ) :
    (∫k,f k∂weightedCoarea d a)=∫k,(a (fullLegs k):ℂ)*f k∂euclideanCircleRegularCoarea d := by
  have hw : Measurable (PinnedMaximalDifference.weight a) :=
    (ha.comp PinnedMollifierRoots.fullLegs_continuous).measurable.ennreal_ofReal
  apply (integral_withDensity_eq_integral_toReal_smul hw
    (Eventually.of_forall (fun _=>ENNReal.ofReal_lt_top)) f).trans
  apply integral_congr_ae
  exact Eventually.of_forall (fun k=>by
    change (ENNReal.ofReal (a (fullLegs k))).toReal • f k= _
    simp only [ENNReal.toReal_ofReal (ha0 _),Complex.real_smul])

theorem weighted_quarter_identity {d : ℝ} (hd0 : 0<d) (hdU : d<1/2)
    {a : FourCircle→ℝ} (ha : Continuous a) (ha0 : ∀q,0≤a q) (hasym : SymmetricWeight a)
    {φ ψ : PinnedPeriodicity.Circle→ℂ} (hφ : Continuous φ)
    (hφ2 : ContDiff ℝ 2 (periodicLift φ)) (hψ : Continuous ψ) (γ : ℝ) :
    (γ/4:ℂ)*(∫k,difference φ k*star (difference ψ k)∂weightedCoarea d a)=
      (γ:ℂ)*(∫k,difference φ k*star (ψ (PinnedLegACCircle.circleLeg 0 k))∂weightedCoarea d a) := by
  rw [weighted_integral ha ha0,weighted_integral ha ha0]
  simpa only [legCurrent,legSource,mul_assoc,mul_left_comm,mul_comm] using
    gamma_quarter_identity hd0 hdU ha hasym hφ hφ2 hψ γ

end
end Resonance.PinnedWeightedReadings
