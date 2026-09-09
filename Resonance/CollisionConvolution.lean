import Resonance.CollisionTranslation
import Resonance.QuadraticCollisionInvariants
import Mathlib.Analysis.Calculus.ContDiff.Convolution

/-! Smoothing is performed by one common translation of the full quartet.
The Fubini step is proved for the actual pairing measure and sharp flags. -/
open Set MeasureTheory Filter
open scoped Convolution ContDiff

namespace Resonance.CollisionConvolution
noncomputable section
open ResonantMeasure ContinuousCollisionInvariants CollisionTranslation QuadraticCollisionInvariants

def smooth (κ f : E → ℝ) : E → ℝ := κ ⋆[ContinuousLinearMap.mul ℝ ℝ] f

theorem smooth_apply (κ f : E → ℝ) (x : E) :
    smooth κ f x = ∫ z, κ z * f (x-z) := rfl

theorem smooth_contDiff {κ f : E → ℝ} (hκ : HasCompactSupport κ)
    (hκs : ContDiff ℝ ∞ κ) (hfi : Integrable f) : ContDiff ℝ ∞ (smooth κ f) :=
  hκ.contDiff_convolution_left (ContinuousLinearMap.mul ℝ ℝ) hκs hfi.locallyIntegrable

theorem smooth_integrand_integrable {κ f : E → ℝ} (hκ : HasCompactSupport κ)
    (hκc : Continuous κ) (hfi : Integrable f) (x : E) :
    Integrable (fun z => κ z*f (x-z)) :=
  hκ.convolutionExists_left (ContinuousLinearMap.mul ℝ ℝ) hκc hfi.locallyIntegrable x

theorem smooth_invariant {r R δ : ℝ} (hr : 0 ≤ r) (hmargin : r+δ ≤ R)
    {κ f : E → ℝ} (hκ : HasCompactSupport κ) (hκc : Continuous κ)
    (hκsupport : Function.support κ ⊆ cube δ)
    (hfm : Measurable f) (hfi : Integrable f) (hf : invariant R f) :
    invariant r (smooth κ f) := by
  letI := pairingMeasure_finite hr
  have hza : ∀ᵐ z ∂(volume : Measure E), ∀ᵐ q ∂pairingMeasure r,
      κ z*f (q 0-z)+κ z*f (q 1-z)=κ z*f (q 2-z)+κ z*f (q 3-z) := by
    apply ae_of_all
    intro z
    by_cases hz : κ z=0
    · exact ae_of_all _ (fun q => by simp [hz])
    · have hzi := invariant_shift hmargin (hκsupport hz) hfm hf
      filter_upwards [hzi] with q hq
      change f (q 0-z)+f (q 1-z)=f (q 2-z)+f (q 3-z) at hq
      linear_combination κ z * hq
  have hjm : MeasurableSet {w : E × FourMomenta |
      κ w.1*f (w.2 0-w.1)+κ w.1*f (w.2 1-w.1)=
      κ w.1*f (w.2 2-w.1)+κ w.1*f (w.2 3-w.1)} :=
    measurableSet_eq_fun (by fun_prop) (by fun_prop)
  have hqa : ∀ᵐ q ∂pairingMeasure r, ∀ᵐ z ∂(volume : Measure E),
      κ z*f (q 0-z)+κ z*f (q 1-z)=κ z*f (q 2-z)+κ z*f (q 3-z) :=
    (Measure.ae_ae_comm hjm).mp hza
  filter_upwards [hqa] with q hq
  have hi (i : Fin 4) := smooth_integrand_integrable hκ hκc hfi (q i)
  change (∫ z, κ z*f (q 0-z))+(∫ z, κ z*f (q 1-z)) =
    (∫ z, κ z*f (q 2-z))+(∫ z, κ z*f (q 3-z))
  rw [← integral_add (hi 0) (hi 1), ← integral_add (hi 2) (hi 3)]
  exact integral_congr_ae hq

theorem smooth_invariant_quadratic {r R δ : ℝ} (hr : 0 < r) (hmargin : r+δ ≤ R)
    {κ f : E → ℝ} (hκ : HasCompactSupport κ) (hκs : ContDiff ℝ ∞ κ)
    (hκsupport : Function.support κ ⊆ cube δ)
    (hfm : Measurable f) (hfi : Integrable f) (hf : invariant R f) :
    ∃ c : ℝ, ∀ x∈openCube r, smooth κ f x = smooth κ f 0 +
      fderiv ℝ (smooth κ f) 0 x + (c/2)*‖x‖^2 := by
  exact differentiable_collision_invariant_quadratic hr
    (fun x _ => (smooth_contDiff hκ hκs hfi).differentiable (by norm_num) x)
    (smooth_invariant hr.le hmargin hκ hκs.continuous hκsupport hfm hfi hf)

end
end Resonance.CollisionConvolution
