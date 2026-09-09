import Resonance.ActualPhasePythagoras
import Resonance.Entropy

/-! Identification with the paper's original f/N - 1 - log(f/N)
relative entropy. Positivity and integrability are both proved explicitly
for the actual continuous phase distributions. -/
open Set MeasureTheory
namespace Resonance.PhaseEntropyDictionary
noncomputable section
open FreeTransport PhaseEnergy PhaseRelativeEntropy PhaseLogEntropy ContinuousLogPath
open Thermodynamics ThermodynamicChart ActualMatchedMoments ActualCoframeWeight
open ActualPhasePythagoras

def originalEntropy (R : ℝ) (f N : Distribution R) : ℝ :=
  Entropy.entropy (phaseMeasure R) f N

theorem original_density_integrable (R : ℝ) (f q : Distribution R)
    (hf : ∀ z,0 < f z) (hq : ∀ z,0 < q z) :
    Integrable (fun z=>Entropy.density (f z) (Ring.inverse q z)) (phaseMeasure R) := by
  have h := continuous_integrable R (f*q-1-logField (f*q))
  apply h.congr
  apply ae_of_all
  intro z
  simp only [ContinuousMap.sub_apply,ContinuousMap.mul_apply,ContinuousMap.one_apply,
    logField_apply (f*q) (fun z=>(mul_pos (hf z) (hq z)).ne'),
    Entropy.density,ring_inverse_apply q (fun z=>(hq z).ne'),div_inv_eq_mul]

theorem relativeEntropy_original (R : ℝ) (f q : Distribution R)
    (hf : ∀ z,0 < f z) (hq : ∀ z,0 < q z) :
    relativeEntropy R f q=originalEntropy R f (Ring.inverse q) := by
  rw [relativeEntropy_integral R f q hf hq]
  apply integral_congr_ae
  apply ae_of_all
  intro z
  dsimp only [Entropy.density]
  rw [ring_inverse_apply q (fun z=>(hq z).ne'),div_inv_eq_mul]

theorem denominatorField_positive (R : ℝ) (a : C(SpatialTorus,Parameter))
    (ha : ∀ X,a X∈positiveDomain R) (z : Phase R) : 0 < denominatorField R a z := by
  change 0 < WeightedPhysicalForm.reciprocalProfile (a z.1) z.2
  rw [WeightedPhysicalForm.reciprocalProfile_eq_inv]
  exact inv_pos.mpr (WeightedJointMeasure.profile_pos (ha z.1) z.2.property)

theorem actual_original_pythagoras (R : ℝ) (hR : 0 < R) (f : Distribution R)
    (hf : ∀ z,0 < f z) (hi : ∀ X,actualMoments R f X∈momentImage R)
    (a : C(SpatialTorus,Parameter)) (ha : ∀ X,a X∈positiveDomain R) :
    originalEntropy R f (Ring.inverse (denominatorField R a))=
      originalEntropy R f
        (Ring.inverse (denominatorField R (matchedField R hR f hi)))+
      originalEntropy R
        (Ring.inverse (denominatorField R (matchedField R hR f hi)))
        (Ring.inverse (denominatorField R a)) := by
  have hq : ∀ z,0 < denominatorField R (matchedField R hR f hi) z :=
    denominatorField_positive R _ (fun X=>matched_positive R hR f X (hi X))
  have hN : ∀ z,0 < Ring.inverse (denominatorField R (matchedField R hR f hi)) z := by
    intro z
    rw [ring_inverse_apply _ (fun z=>(hq z).ne')]
    exact inv_pos.mpr (hq z)
  rw [←relativeEntropy_original R f _ hf (denominatorField_positive R a ha),
    ←relativeEntropy_original R f _ hf hq,
    ←relativeEntropy_original R _ _ hN (denominatorField_positive R a ha)]
  exact actual_matched_phase_pythagoras R hR f hi a

end
end Resonance.PhaseEntropyDictionary
