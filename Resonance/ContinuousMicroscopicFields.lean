import Resonance.ContinuousLogPath
import Resonance.MicroscopicCoordinates
import Resonance.ContinuousSourceMultiplication

/-! Original continuous microscopic coordinates. The algebra is performed
before passage to the fixed reference Hilbert space, so the complete
five-moment constraint retains the same distribution and matched profile. -/
namespace Resonance.ContinuousMicroscopicFields
noncomputable section
open ResonantMeasure ContinuousLogPath MicroscopicCoordinates

def zField {R : ℝ} (c : ℝ) (f Nc : C(cube R,ℝ)) : C(cube R,ℝ) :=
  c • (1-Nc*Ring.inverse f)

def yField {R : ℝ} (c : ℝ) (f N Nc : C(cube R,ℝ)) : C(cube R,ℝ) :=
  (N*Ring.inverse Nc)*zField c f Nc

def bField {R : ℝ} (f N Nc : C(cube R,ℝ)) : C(cube R,ℝ) :=
  (f*Nc)*Ring.inverse (N*N)

theorem zField_apply {R : ℝ} (c : ℝ) (f Nc : C(cube R,ℝ))
    (hf : ∀ k,f k≠0) (k : cube R) :
    zField c f Nc k=reciprocalMicro c (f k) (Nc k) := by
  simp only [zField,ContinuousMap.smul_apply,ContinuousMap.sub_apply,
    ContinuousMap.one_apply,ContinuousMap.mul_apply,ring_inverse_apply f hf,
    smul_eq_mul,reciprocalMicro,div_eq_mul_inv]

theorem yField_apply {R : ℝ} (c : ℝ) (f N Nc : C(cube R,ℝ))
    (hf : ∀ k,f k≠0) (hNc : ∀ k,Nc k≠0) (k : cube R) :
    yField c f N Nc k=referenceMicro c (f k) (N k) (Nc k) := by
  simp only [yField,ContinuousMap.mul_apply,ring_inverse_apply Nc hNc,
    zField_apply c f Nc hf,referenceMicro,div_eq_mul_inv]

theorem bField_apply {R : ℝ} (f N Nc : C(cube R,ℝ))
    (hN : ∀ k,N k≠0) (k : cube R) :
    bField f N Nc k=matchingWeight (f k) (N k) (Nc k) := by
  have hNN : ∀ k,(N*N) k≠0 := fun k=>mul_ne_zero (hN k) (hN k)
  simp only [bField,ContinuousMap.mul_apply,ring_inverse_apply (N*N) hNN,
    matchingWeight,pow_two,div_eq_mul_inv]

theorem weighted_matching_field {R : ℝ} (c : ℝ) (f N Nc : C(cube R,ℝ))
    (hf : ∀ k,f k≠0) (hN : ∀ k,N k≠0) (hNc : ∀ k,Nc k≠0) :
    N*(bField f N Nc*yField c f N Nc)=c • (f-Nc) := by
  ext k
  simp only [ContinuousMap.mul_apply,ContinuousMap.smul_apply,
    ContinuousMap.sub_apply,smul_eq_mul,bField_apply f N Nc hN,
    yField_apply c f N Nc hf hNc]
  exact (mul_assoc _ _ _).symm.trans (weighted_matching_identity c (f k) (N k)
    (Nc k) (hf k) (hN k) (hNc k))

theorem bField_positive {R : ℝ} (f N Nc : C(cube R,ℝ))
    (hf : ∀ k,0<f k) (hN : ∀ k,N k≠0) (hNc : ∀ k,0<Nc k) (k : cube R) :
    0<bField f N Nc k := by
  rw [bField_apply f N Nc hN]
  exact matchingWeight_positive (hf k) (hN k) (hNc k)

end
end Resonance.ContinuousMicroscopicFields
