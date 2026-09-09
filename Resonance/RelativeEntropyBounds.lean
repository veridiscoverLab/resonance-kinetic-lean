import Resonance.PhaseRelativeEntropy
import Resonance.Entropy

/-! Explicit quadratic control of the original entropy density and of
the two microscopic coordinates, with all positive lower bounds visible. -/
namespace Resonance.RelativeEntropyBounds
noncomputable section
open FreeTransport PhaseEnergy PhaseRelativeEntropy ContinuousLogPath MeasureTheory

theorem density_upper {d : ℝ} (hd : 0 < d) :
    d-1-Real.log d ≤ (d-1)^2/d := by
  have h := Real.log_le_sub_one_of_pos (inv_pos.mpr hd)
  rw [Real.log_inv] at h
  have he : (d-1)^2/d = d-2+d⁻¹ := by field_simp; ring
  rw [he]
  linarith

theorem density_interval_upper {d m : ℝ} (hm : 0 < m) (hd : m ≤ d) :
    d-1-Real.log d ≤ m⁻¹*(d-1)^2 := by
  have hp := lt_of_lt_of_le hm hd
  calc
    _ ≤ (d-1)^2/d := density_upper hp
    _ ≤ (d-1)^2/m := div_le_div_of_nonneg_left (sq_nonneg _) hm hd
    _ = _ := by rw [div_eq_mul_inv,mul_comm]

theorem physical_density_upper {f q m M : ℝ} (hf : 0 < f) (hq : 0 < q)
    (hm : 0 < m) (hfm : m ≤ f) (hqM : q ≤ M) :
    f*q-1-Real.log (f*q) ≤ (M/m)*(f-q⁻¹)^2 := by
  have he : (f*q-1)^2/(f*q)=(q/f)*(f-q⁻¹)^2 := by
    field_simp
  calc
    _ ≤ (f*q-1)^2/(f*q) := density_upper (mul_pos hf hq)
    _ = (q/f)*(f-q⁻¹)^2 := he
    _ ≤ (M/m)*(f-q⁻¹)^2 := by
      apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
      exact (div_le_div_of_nonneg_left hq.le hm hfm).trans
        (div_le_div_of_nonneg_right hqM hm.le)

theorem reciprocal_coordinate_difference {d : ℝ} (hd : d≠0) :
    (d-1)-(1-d⁻¹)=d*(1-d⁻¹)^2 := by
  field_simp

theorem relativeEntropy_nonnegative (R : ℝ) (f q : Distribution R)
    (hf : ∀ z,0 < f z) (hq : ∀ z,0 < q z) : 0 ≤ relativeEntropy R f q := by
  rw [relativeEntropy_integral R f q hf hq]
  apply integral_nonneg
  intro z
  exact sub_nonneg.mpr (Real.log_le_sub_one_of_pos (mul_pos (hf z) (hq z)))

theorem relativeEntropy_quadratic_bound (R : ℝ) (f q : Distribution R)
    (hf : ∀ z,0 < f z) (hq : ∀ z,0 < q z)
    {m M : ℝ} (hm : 0 < m) (hfm : ∀ z,m ≤ f z) (hqM : ∀ z,q z ≤ M) :
    relativeEntropy R f q ≤ (M/m)*integralCLM R ((f-Ring.inverse q)^2) := by
  rw [relativeEntropy_integral R f q hf hq]
  have hlo := continuous_integrable R (f*q-1-logField (f*q))
  have hhi := (continuous_integrable R ((f-Ring.inverse q)^2)).const_mul (M/m)
  have helo : (↑(f*q-1-logField (f*q)) : Phase R→ℝ)=
      (fun z=>f z*q z-1-Real.log (f z*q z)) := by
    funext z
    simp only [ContinuousMap.sub_apply,ContinuousMap.mul_apply,ContinuousMap.one_apply,
      logField_apply (f*q) (fun z=>(mul_pos (hf z) (hq z)).ne')]
  rw [helo] at hlo
  change (∫ z,f z*q z-1-Real.log (f z*q z) ∂phaseMeasure R) ≤
    (M/m)*(∫ z,((f-Ring.inverse q)^2) z ∂phaseMeasure R)
  rw [←integral_const_mul]
  apply integral_mono_ae hlo hhi
  apply ae_of_all
  intro z
  simpa only [ContinuousMap.pow_apply,ContinuousMap.sub_apply,
    ring_inverse_apply q (fun z=>(hq z).ne')] using
    physical_density_upper (hf z) (hq z) hm (hfm z) (hqM z)

end
end Resonance.RelativeEntropyBounds
