import Resonance.RealMatrixComplexification

/-! Scalar extension preserves the injectivity of the actual real Gram map. -/
namespace Resonance.ComplexMatrixInjection
noncomputable section
open RealMatrixComplexification

def embedVector {I : Type*} (v : I→ℝ) : I→ℂ := fun i=>(v i : ℂ)

theorem original_mulVec_embed {I : Type*} [Fintype I] (M : Matrix I I ℝ) (v : I→ℝ) :
    (complexify M).mulVec (embedVector v)=embedVector (M.mulVec v) := by
  funext i
  apply Complex.ext
  · rw [mulVec_re]
    rfl
  · rw [mulVec_im]
    simp [embedVector,Matrix.mulVec,dotProduct]

theorem original_injective_complex {I : Type*} [Fintype I] (M : Matrix I I ℝ)
    (hi : Function.Injective M.mulVec) : Function.Injective (complexify M).mulVec := by
  intro z w he
  have hr : M.mulVec (fun i=>(z i).re)=M.mulVec (fun i=>(w i).re) := by
    funext i
    rw [←mulVec_re,←mulVec_re,he]
  have him : M.mulVec (fun i=>(z i).im)=M.mulVec (fun i=>(w i).im) := by
    funext i
    rw [←mulVec_im,←mulVec_im,he]
  have hre := hi hr
  have hie := hi him
  funext i
  exact Complex.ext (congrFun hre i) (congrFun hie i)

theorem embed_smul {I : Type*} (a : ℝ) (v : I→ℝ) :
    embedVector (a • v)=(a : ℂ) • embedVector v := by
  funext i
  simp [embedVector]

end
end Resonance.ComplexMatrixInjection
