import Resonance.PinnedRJProfile
import Resonance.PinnedPhysicalUniform

/-! The compact positive two-parameter RJ statement uses its actual
quartet weight and original physical L² projection throughout. -/
open Set
namespace Resonance.PinnedRJUniform
noncomputable section
open PinnedRJProfile PinnedPhysicalForm PinnedPhysicalGap PinnedMaximalDifference

theorem actual_compact_RJ_physical_gap {d : ℝ} (hd0 : 0 < d) (hdU : d < 1/2)
    {K : Set Parameter} (hK : IsCompact K) (hpos : K⊆positiveDomain d) :
    ∃ lam : ℝ, 0 < lam ∧ ∀ p : K, ∀ (γ : ℝ), 0 ≤ γ →
      ∀ u : PhysicalDomain hd0 hdU (profile hd0 hdU ⟨p.val,hpos p.property⟩)
        (profile_positive hd0 hdU ⟨p.val,hpos p.property⟩),
        (γ/4)*lam*‖(u : Source)-(physicalNull hd0 hdU
          (profile hd0 hdU ⟨p.val,hpos p.property⟩)
          (profile_positive hd0 hdU ⟨p.val,hpos p.property⟩)).starProjection u‖^2
          ≤ (physicalForm hd0 hdU (profile hd0 hdU ⟨p.val,hpos p.property⟩)
            (profile_positive hd0 hdU ⟨p.val,hpos p.property⟩) γ u u).re := by
  obtain ⟨b,C,hb,hC,hbounds⟩ := compact_positive_bounds hd0 hdU hK hpos
  obtain ⟨lam,hlam,hgap⟩ := PinnedPhysicalUniform.physical_uniform_bound hd0 hdU hb hC
  exact ⟨lam,hlam,fun p => hgap _ _ (hbounds p).1 (hbounds p).2⟩

end
end Resonance.PinnedRJUniform
