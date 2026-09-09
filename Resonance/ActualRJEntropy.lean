import Resonance.PhaseRelativeEntropy
import Resonance.CoframeEntropyCancellation

/-! An actual local RJ distribution is its own five-moment match.
Consequently the initial microscopic entropy is exactly zero. -/
open Set MeasureTheory
namespace Resonance.ActualRJEntropy
noncomputable section
open FreeTransport PhaseEnergy JetCollision ContinuousCollisionMoments
open ActualMatchedMoments Thermodynamics ThermodynamicChart WeightedJointMeasure
open ActualCoframeWeight CoframeEntropyCancellation PhaseRelativeEntropy
open WeightedPhysicalForm

theorem matchedValue_of_localRJ (R : ℝ) (hR : 0 < R) (f : Distribution R)
    (θ : SpatialTorus→Parameter) (hθ : ∀ X,θ X∈positiveDomain R)
    (hf : ∀ z,f z=profile (θ z.1) z.2) (X : SpatialTorus) :
    matchedValue R hR f X=θ X := by
  have he : f.curry X=ActualMatchedMoments.rjCube R (θ X) (hθ X) := by
    ext k
    exact hf (X,k)
  change momentInverse R hR (moments R (f.curry X))=θ X
  rw [he,rjCube_moments,momentInverse_left R hR (θ X) (hθ X)]

theorem actual_localRJ_entropy_zero (R : ℝ) (hR : 0 < R) (f : Distribution R)
    (θ : SpatialTorus→Parameter) (hθ : ∀ X,θ X∈positiveDomain R)
    (hf : ∀ z,f z=profile (θ z.1) z.2)
    (hi : ∀ X,actualMoments R f X∈momentImage R) :
    relativeEntropy R f (denominatorField R (matchedField R hR f hi))=0 := by
  have hp : ∀ z,0 < f z := fun z=>(hf z).symm ▸ profile_pos (hθ z.1) z.2.property
  have hq : ∀ z,0 < denominatorField R (matchedField R hR f hi) z := by
    intro z
    change 0 < reciprocalProfile (matchedValue R hR f z.1) z.2
    rw [matchedValue_of_localRJ R hR f θ hθ hf z.1,reciprocalProfile_eq_inv]
    exact inv_pos.mpr (profile_pos (hθ z.1) z.2.property)
  rw [relativeEntropy_integral R _ _ hp hq]
  apply integral_eq_zero_of_ae
  apply ae_of_all
  intro z
  change f z*reciprocalProfile (matchedValue R hR f z.1) z.2-1-
    Real.log (f z*reciprocalProfile (matchedValue R hR f z.1) z.2)=0
  rw [matchedValue_of_localRJ R hR f θ hθ hf z.1,reciprocalProfile_eq_inv,←hf z,
    mul_inv_cancel₀ (hp z).ne']
  simp

theorem coframe_entropy_zero_of_localRJ (R : ℝ) (hR : 0 < R) (s : Set ℝ) (p : ℝ→Space R)
    (hi : ∀ t∈s,∀ X,actualMoments R (readback (p t)) X∈momentImage R)
    {t : ℝ} (ht : t∈s) (θ : SpatialTorus→Parameter) (hθ : ∀ X,θ X∈positiveDomain R)
    (hf : ∀ z,readback (p t) z=profile (θ z.1) z.2) :
    relativeEntropy R (readback (p t)) (readback (coframeJet R hR s p hi t))=0 := by
  rw [coframeJet_matchedField R hR s p hi ht]
  exact actual_localRJ_entropy_zero R hR _ θ hθ hf (hi t ht)

end
end Resonance.ActualRJEntropy
