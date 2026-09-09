import Resonance.GramCouplingVariance
import Resonance.ThermodynamicJets

/-! Continuity is derived from the original weighted cube integrals, so
compact parameter bounds do not assume a matrix-valued constitutive law. -/
open MeasureTheory Set
open scoped BigOperators ContDiff
namespace Resonance.GramCoefficientContinuity
noncomputable section
open Entropy Thermodynamics ThermodynamicJets GramCouplingVariance ActualEulerCoupling

theorem original_gram_power_integral (R : ℝ) (θ : Parameter) (i j : Fin 5) :
    gramMatrix R θ i j=powerIntegral R 1 (fun k=>fiveInvariants i k*fiveInvariants j k) θ := by
  unfold gramMatrix powerIntegral
  apply integral_congr_ae
  filter_upwards [] with k
  ring

theorem original_gram_continuousOn (R : ℝ) :
    ContinuousOn (gramMatrix R) (positiveDomain R) := by
  apply continuousOn_pi.mpr
  intro i
  apply continuousOn_pi.mpr
  intro j
  have hh := (powerIntegral_contDiffOn_finite R 0 1
    (fun k=>fiveInvariants i k*fiveInvariants j k)
    ((fiveInvariants_continuous i).mul (fiveInvariants_continuous j))).continuousOn
  simpa only [original_gram_power_integral] using hh

theorem quadratic_continuous :
    Continuous (fun p : (Matrix (Fin 5) (Fin 5) ℝ)×Parameter=>quadratic p.1 p.2) := by
  unfold quadratic Matrix.mulVec dotProduct
  fun_prop

theorem cross_continuous :
    Continuous (fun p : (Matrix (Fin 5) (Fin 5) ℝ)×(Parameter×Parameter)=>cross p.1 p.2.1 p.2.2) := by
  unfold cross Matrix.mulVec dotProduct
  fun_prop

theorem betaDirection_continuous : Continuous betaDirection := by
  apply continuous_pi
  intro i
  fin_cases i
  · exact continuous_const
  · exact continuous_apply 0
  · exact continuous_apply 1
  · exact continuous_apply 2
  · exact continuous_const

theorem original_variance_continuousOn (R : ℝ) (hR : 0<R) :
    ContinuousOn (fun p : Parameter×(Fin 3→ℝ)=>variance R p.1 p.2)
      ((positiveDomain R)×ˢuniv) := by
  have hm : ContinuousOn (fun p : Parameter×(Fin 3→ℝ)=>gramMatrix R p.1)
      ((positiveDomain R)×ˢuniv) :=
    (original_gram_continuousOn R).comp continuous_fst.continuousOn (fun _ h=>h.1)
  have hb : Continuous (fun p : Parameter×(Fin 3→ℝ)=>betaDirection p.2) :=
    betaDirection_continuous.comp continuous_snd
  have ha : Continuous (fun _ : Parameter×(Fin 3→ℝ)=>ActualFourierRank.massDirection) :=
    continuous_const
  have hq := quadratic_continuous.comp_continuousOn (hm.prodMk hb.continuousOn)
  have hc := cross_continuous.comp_continuousOn
    (hm.prodMk (ha.prodMk hb).continuousOn)
  have hmass := quadratic_continuous.comp_continuousOn (hm.prodMk ha.continuousOn)
  exact hq.sub ((hc.pow 2).div hmass (fun p hp=>(actual_mass_gram_pos R hR p.1 hp.1).ne'))

end
end Resonance.GramCoefficientContinuity
