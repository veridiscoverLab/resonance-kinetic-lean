import Resonance.Collision

/-! Exact identities for the same original and matched distributions.
These coordinates connect actual moment matching, entropy work, and the
signed complete current; all four legs use one common matched equilibrium. -/
namespace Resonance.MicroscopicCoordinates
noncomputable section
open Collision

def reciprocalMicro (c f Nc : ℝ) : ℝ := c*(1-Nc/f)
def referenceMicro (c f N Nc : ℝ) : ℝ := (N/Nc)*reciprocalMicro c f Nc
def matchingWeight (f N Nc : ℝ) : ℝ := f*Nc/N^2

theorem weighted_matching_identity (c f N Nc : ℝ) (hf : f≠0) (hN : N≠0) (hNc : Nc≠0) :
    N*matchingWeight f N Nc*referenceMicro c f N Nc=c*(f-Nc) := by
  unfold matchingWeight referenceMicro reciprocalMicro
  field_simp

theorem physical_micro_identity (c f Nc : ℝ) (hf : f≠0) (hNc : Nc≠0) :
    c*(f-Nc)=Nc*(f/Nc)*reciprocalMicro c f Nc := by
  unfold reciprocalMicro
  field_simp

theorem divided_referenceMicro (c f N Nc : ℝ) (hf : f≠0) (hN : N≠0) (hNc : Nc≠0) :
    referenceMicro c f N Nc/N=c*(Nc⁻¹-f⁻¹) := by
  unfold referenceMicro reciprocalMicro
  field_simp

theorem reference_to_reciprocal (c f N Nc u : ℝ) (hN : N≠0) (hNc : Nc≠0) :
    reciprocalMicro c f Nc-u=(Nc/N)*(referenceMicro c f N Nc-u)+(Nc/N-1)*u := by
  unfold referenceMicro
  field_simp
  ring

theorem entropy_work_identity (c f Nc A : ℝ) (hf : f≠0) :
    c*(f-Nc)*A=reciprocalMicro c f Nc*(f*A) := by
  unfold reciprocalMicro
  field_simp

theorem coordinate_error_identity (c f Nc : ℝ) (hf : f≠0) (hNc : Nc≠0) :
    c*(f/Nc-1)-reciprocalMicro c f Nc=c*(f/Nc)*(1-Nc/f)^2 := by
  unfold reciprocalMicro
  field_simp

theorem matchingWeight_positive {f N Nc : ℝ} (hf : 0 < f) (hN : N≠0) (hNc : 0 < Nc) :
    0 < matchingWeight f N Nc := div_pos (mul_pos hf hNc) (sq_pos_of_ne_zero hN)

theorem full_difference_identity (c : ℝ) (f N Nc : Quartet)
    (hf : ∀ i,f i≠0) (hN : ∀ i,N i≠0) (hNc : ∀ i,Nc i≠0)
    (he : delta (fun i=>(Nc i)⁻¹)=0) :
    delta (fun i=>referenceMicro c (f i) (N i) (Nc i)/N i)=
      -c*delta (fun i=>(f i)⁻¹) := by
  have hpoint (i : Fin 4) := divided_referenceMicro c (f i) (N i) (Nc i) (hf i) (hN i) (hNc i)
  simp_rw [hpoint]
  have hid : delta (fun i=>c*((Nc i)⁻¹-(f i)⁻¹))=
      c*(delta (fun i=>(Nc i)⁻¹)-delta (fun i=>(f i)⁻¹)) := by unfold delta; ring
  rw [hid,he]
  ring

end
end Resonance.MicroscopicCoordinates
