import Resonance.ActualCoframeWeight
import Resonance.ContinuousLogPath

/-! Actual five-moment matching annihilates every parameter test in
the same phase integral. This pays the moving-coframe entropy term. -/
open Set MeasureTheory
namespace Resonance.ContinuousMomentPairing
noncomputable section
open FreeTransport PhaseEnergy ContinuousCollisionMoments ActualMatchedMoments
open ActualCoframeWeight Thermodynamics ThermodynamicChart WeightedPhysicalForm
open ContinuousLogPath

theorem moment_eq_dot_moments (R : ℝ) (θ : Parameter) (f : CubeFunction R) :
    moment R θ f=∑ i : Fin 5,θ i*moments R f i := by
  rw [moment_integral]
  have he (k : MomentumDomain R) : reciprocalProfile θ k*f k=
      ∑ i : Fin 5,θ i*(Entropy.fiveInvariants i (WeightedJointMeasure.coordinates k)*f k) := by
    simp only [reciprocalProfile,Entropy.denominator,Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    ring
  simp_rw [he]
  rw [integral_finset_sum]
  · apply Finset.sum_congr rfl
    intro i _
    rw [integral_const_mul,moments_integral]
  · intro i _
    have h := cube_continuous_integrable R (momentTest R (basisParameter i)*f)
    have hh := h.const_mul (θ i)
    simpa only [ContinuousMap.mul_apply,momentTest,ContinuousMap.coe_mk,basis_reciprocal] using hh

theorem moment_zero_of_moments_zero (R : ℝ) (θ : Parameter) (f : CubeFunction R)
    (hf : moments R f=0) : moment R θ f=0 := by
  rw [moment_eq_dot_moments,hf]
  simp

theorem matched_parameter_pairing_zero (R : ℝ) (hR : 0 < R) (f : Distribution R)
    (hf : ∀ X,actualMoments R f X∈momentImage R)
    (a : C(SpatialTorus,Parameter)) :
    integralCLM R (denominatorField R a*
      (f-Ring.inverse (denominatorField R (matchedField R hR f hf))))=0 := by
  let q := denominatorField R (matchedField R hR f hf)
  have hq : ∀ z,q z≠0 := by
    intro z
    change reciprocalProfile (matchedValue R hR f z.1) z.2≠0
    rw [reciprocalProfile_eq_inv]
    exact inv_ne_zero (WeightedJointMeasure.profile_pos
      (matched_positive R hR f z.1 (hf z.1)) z.2.property).ne'
  change (∫ z,(denominatorField R a*(f-Ring.inverse q)) z ∂phaseMeasure R)=0
  rw [phaseMeasure,integral_prod _ (continuous_integrable R _)]
  apply integral_eq_zero_of_ae
  apply ae_of_all
  intro X
  let N := rjCube R (matchedValue R hR f X) (matched_positive R hR f X (hf X))
  have he (k : MomentumDomain R) : Ring.inverse q (X,k)=N k := by
    rw [ring_inverse_apply q hq]
    change (reciprocalProfile (matchedValue R hR f X) k)⁻¹=N k
    rw [reciprocalProfile_eq_inv,inv_inv]
    rfl
  have hm := moment_zero_of_moments_zero R (a X) (f.curry X-N)
    (matched_micro_moments_zero R hR f X (hf X))
  change (∫ k,reciprocalProfile (a X) k*(f (X,k)-Ring.inverse q (X,k)) ∂momentumMeasure R)=0
  simp_rw [he]
  exact hm

end
end Resonance.ContinuousMomentPairing
