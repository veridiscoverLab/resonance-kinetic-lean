import Resonance.CoareaIsometry
import Resonance.RegularNormalizedLimit

/-! Actual Euclidean coordinate permutations for arbitrary nonzero gradient
components, preserving both volume and normalized coarea. -/
open Set MeasureTheory
open scoped ENNReal InnerProductSpace
namespace Resonance.CoordinatePermutation
noncomputable section
open LinearSurfaceArea

def swapMiddle (i : Fin 3) : A ≃ₗᵢ[ℝ] A :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (Equiv.swap 1 i)

theorem swapMiddle_apply (i j : Fin 3) (p : A) : swapMiddle i p j=p (Equiv.swap 1 i j) := by
  rfl

theorem swapMiddle_symm_apply (i j : Fin 3) (p : A) : (swapMiddle i).symm p j=p (Equiv.swap 1 i j) := by
  have he : (swapMiddle i).symm p=swapMiddle i p := by
    apply (swapMiddle i).injective
    rw [(swapMiddle i).apply_symm_apply]
    ext k
    simp only [swapMiddle_apply,Equiv.swap_apply_self]
  rw [he,swapMiddle_apply]

theorem swapMiddle_gradient {g : A → A} (p : A) (i : Fin 3) :
    ((swapMiddle i).symm (g (swapMiddle i ((swapMiddle i).symm p)))) 1=g p i := by
  rw [(swapMiddle i).apply_symm_apply,swapMiddle_symm_apply,Equiv.swap_apply_left]

theorem compact_pullback {E : Type*} [Zero E] (e : A ≃ₗᵢ[ℝ] A)
    {B : A → E} (hK : HasCompactSupport B) : HasCompactSupport (B ∘ e) := by
  apply HasCompactSupport.of_support_subset_isCompact (hK.image e.symm.continuous)
  intro p hp
  exact ⟨e p,subset_tsupport B hp,e.symm_apply_apply p⟩

theorem tsupport_pullback {E : Type*} [Zero E] (e : A ≃ₗᵢ[ℝ] A) (B : A → E) :
    tsupport (B ∘ e)⊆e ⁻¹' tsupport B := by
  apply closure_minimal
  · intro p hp
    exact subset_tsupport B hp
  · exact (isClosed_tsupport B).preimage e.continuous

theorem pullback_support_source {E : Type*} [Zero E] (e : A ≃ₗᵢ[ℝ] A)
    {B : A → E} {S : Set A} (hS : tsupport B⊆e '' S) : tsupport (B ∘ e)⊆S := by
  intro p hp
  obtain ⟨q,hq,heq⟩ := hS (tsupport_pullback e B hp)
  exact e.injective heq ▸ hq

theorem image_inter_level (e : A ≃ₗᵢ[ℝ] A) (F : A → ℝ) (S : Set A) :
    e '' (S∩{p|(F ∘ e) p=0})=(e '' S)∩{p|F p=0} := by
  ext p
  constructor
  · rintro ⟨q,⟨hq,hF⟩,rfl⟩
    exact ⟨⟨q,hq,rfl⟩,hF⟩
  · rintro ⟨⟨q,hq,rfl⟩,hF⟩
    exact ⟨q,⟨hq,hF⟩,rfl⟩

end
end Resonance.CoordinatePermutation
