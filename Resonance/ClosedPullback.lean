import Resonance.ClosedOperatorRepresentation

/-! A closed, densely defined difference operator may be pulled back
through a bounded linear equivalence. No isometry is required or inferred. -/
open Set LinearPMap
namespace Resonance.ClosedPullback
noncomputable section
variable {H J : Type*} [NormedAddCommGroup H] [NormedAddCommGroup J]
  [InnerProductSpace ℂ H] [InnerProductSpace ℂ J]

def domainMap (T : H→ₗ.[ℂ]J) (U : H≃L[ℂ]H) :
    T.domain.comap U.toLinearMap→ₗ[ℂ]T.domain where
  toFun x := ⟨U x,x.property⟩
  map_add' x y := by apply Subtype.ext; exact U.map_add _ _
  map_smul' c x := by apply Subtype.ext; exact U.map_smul c _

def pullback (T : H→ₗ.[ℂ]J) (U : H≃L[ℂ]H) : H→ₗ.[ℂ]J where
  domain := T.domain.comap U.toLinearMap
  toFun := T.toFun.comp (domainMap T U)

theorem domain_iff (T : H→ₗ.[ℂ]J) (U : H≃L[ℂ]H) (x : H) :
    x∈(pullback T U).domain ↔ U x∈T.domain := Iff.rfl

theorem pullback_apply (T : H→ₗ.[ℂ]J) (U : H≃L[ℂ]H)
    (x : (pullback T U).domain) : pullback T U x=T ⟨U x,x.property⟩ := rfl

theorem graph_iff (T : H→ₗ.[ℂ]J) (U : H≃L[ℂ]H) (x : H) (z : J) :
    (x,z)∈(pullback T U).graph ↔ (U x,z)∈T.graph := by
  constructor
  · intro hp
    obtain ⟨v,hv,hz⟩ := (LinearPMap.mem_graph_iff _).mp hp
    apply (LinearPMap.mem_graph_iff _).mpr
    refine ⟨domainMap T U v,?_,hz⟩
    change U (v : H)=U x
    exact congrArg U hv
  · intro hp
    obtain ⟨v,hv,hz⟩ := (LinearPMap.mem_graph_iff _).mp hp
    change (v : H)=U x at hv
    have hx : U x∈T.domain := hv ▸ v.property
    have he : domainMap T U ⟨x,hx⟩=v := Subtype.ext hv.symm
    apply (LinearPMap.mem_graph_iff _).mpr
    refine ⟨⟨x,hx⟩,rfl,?_⟩
    change T (domainMap T U ⟨x,hx⟩)=z
    rw [he,hz]

theorem pullback_closed (T : H→ₗ.[ℂ]J) (hT : T.IsClosed) (U : H≃L[ℂ]H) :
    (pullback T U).IsClosed := by
  change IsClosed ((pullback T U).graph : Set (H×J))
  have he : ((pullback T U).graph : Set (H×J))=
      (fun p : H×J=>(U p.1,p.2))⁻¹'(T.graph : Set (H×J)) := by
    ext p
    exact graph_iff T U p.1 p.2
  rw [he]
  exact hT.preimage ((U.continuous.comp continuous_fst).prodMk continuous_snd)

theorem pullback_dense (T : H→ₗ.[ℂ]J) (hT : Dense (T.domain : Set H))
    (U : H≃L[ℂ]H) : Dense ((pullback T U).domain : Set H) := by
  change Dense (U⁻¹'(T.domain : Set H))
  exact hT.preimage U.toHomeomorph.isOpenMap

theorem pullback_square_selfAdjoint [CompleteSpace H] [CompleteSpace J]
    (T : H→ₗ.[ℂ]J) (hTc : T.IsClosed) (hTd : Dense (T.domain : Set H))
    (U : H≃L[ℂ]H) :
    IsSelfAdjoint (ClosedOperatorRepresentation.square (pullback T U)) :=
  ClosedOperatorRepresentation.square_selfAdjoint _ (pullback_dense T hTd U)
    (pullback_closed T hTc U)

end
end Resonance.ClosedPullback
