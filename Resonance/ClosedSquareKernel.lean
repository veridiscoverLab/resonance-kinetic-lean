import Resonance.ClosedOperatorRepresentation

/-! The exact zero graph of the actual adjoint square. -/
open Set LinearPMap
namespace Resonance.ClosedSquareKernel
noncomputable section
variable {H J : Type*} [NormedAddCommGroup H] [NormedAddCommGroup J]
  [InnerProductSpace ℂ H] [InnerProductSpace ℂ J] [CompleteSpace H]

theorem square_zero_graph_iff (T : H →ₗ.[ℂ] J) (hT : Dense (T.domain : Set H)) (x : H) :
    (x,0) ∈ (ClosedOperatorRepresentation.square T).graph ↔ (x,0) ∈ T.graph := by
  rw [ClosedOperatorRepresentation.square_graph_iff T hT]
  constructor
  · rintro ⟨hx,hv⟩
    have hh := hv ⟨x,hx⟩
    rw [inner_zero_left] at hh
    have hz : T ⟨x,hx⟩=0 := (inner_self_eq_zero (𝕜:=ℂ)).mp hh.symm
    exact (LinearPMap.mem_graph_iff _).mpr ⟨⟨x,hx⟩,rfl,hz⟩
  · intro hg
    obtain ⟨u,hu,hz⟩ := (LinearPMap.mem_graph_iff _).mp hg
    change (u : H)=x at hu
    have hx : x∈T.domain := hu ▸ u.property
    have he : (⟨x,hx⟩ : T.domain)=u := Subtype.ext hu.symm
    refine ⟨hx,fun y=>?_⟩
    rw [he,hz,inner_zero_left,inner_zero_left]

end
end Resonance.ClosedSquareKernel
