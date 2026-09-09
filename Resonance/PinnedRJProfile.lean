import Resonance.PinnedPhysicalMultiplier

/-! The actual two-parameter positive pinned Rayleigh--Jeans profile
and its joint parameter/quartet continuity. -/
open Set MeasureTheory
namespace Resonance.PinnedRJProfile
noncomputable section
open PinnedPeriodicity PinnedEndToEnd PinnedPhysicalMultiplier PinnedMaximalDifference
local notation "Circle" => PinnedPeriodicity.Circle
local instance periodPositive : Fact (0 < period) := ⟨period_pos⟩

abbrev Parameter := ℝ × ℝ
def positiveDomain (d : ℝ) : Set Parameter := {p | ∀ x : Circle, 0 < p.1+p.2*circleDispersion d x}

def profile {d : ℝ} (hd0 : 0 < d) (hdU : d < 1/2)
    (p : positiveDomain d) : C(Circle,ℝ) where
  toFun x := (p.val.1+p.val.2*circleDispersion d x)⁻¹
  continuous_toFun := (continuous_const.add
    (continuous_const.mul (circleDispersion_continuous hd0 hdU))).inv₀
      (fun x => (p.property x).ne')

theorem profile_positive {d : ℝ} (hd0 : 0 < d) (hdU : d < 1/2)
    (p : positiveDomain d) (x : Circle) : 0 < profile hd0 hdU p x :=
  inv_pos.mpr (p.property x)

theorem profile_inverse {d : ℝ} (hd0 : 0 < d) (hdU : d < 1/2)
    (p : positiveDomain d) (x : Circle) :
    (profile hd0 hdU p x)⁻¹=p.val.1+p.val.2*circleDispersion d x := by
  simp [profile]

theorem profile_joint_continuous {d : ℝ} (hd0 : 0 < d) (hdU : d < 1/2) :
    Continuous (fun q : positiveDomain d × Circle => profile hd0 hdU q.1 q.2) := by
  have h1 : Continuous (fun q : positiveDomain d × Circle => q.1.val.1) :=
    continuous_fst.comp (continuous_subtype_val.comp continuous_fst)
  have h2 : Continuous (fun q : positiveDomain d × Circle => q.1.val.2) :=
    continuous_snd.comp (continuous_subtype_val.comp continuous_fst)
  exact (h1.add (h2.mul ((circleDispersion_continuous hd0 hdU).comp continuous_snd))).inv₀
    (fun q => (q.1.property q.2).ne')

theorem profile_continuous {d : ℝ} (hd0 : 0 < d) (hdU : d < 1/2) :
    Continuous (profile hd0 hdU) :=
  ContinuousMap.continuous_of_continuous_uncurry _ (profile_joint_continuous hd0 hdU)

theorem physicalWeight_joint_continuous {d : ℝ} (hd0 : 0 < d) (hdU : d < 1/2) :
    Continuous (fun q : positiveDomain d × FourCircle => physicalWeight d (profile hd0 hdU q.1) q.2) := by
  apply continuous_finset_prod
  intro i _
  have hm : Continuous (fun q : positiveDomain d × FourCircle => (q.1,q.2 i)) :=
    continuous_fst.prodMk ((continuous_apply i).comp continuous_snd)
  have hn := (profile_joint_continuous hd0 hdU).comp hm
  exact hn.div ((circleDispersion_continuous hd0 hdU).comp ((continuous_apply i).comp continuous_snd))
    (fun q => (dispersion_positive hd0 hdU (q.2 i)).ne')

theorem compact_positive_bounds {d : ℝ} (hd0 : 0 < d) (hdU : d < 1/2)
    {K : Set Parameter} (hK : IsCompact K) (hpos : K⊆positiveDomain d) :
    ∃ b C : ℝ, 0 < b ∧ 0 < C ∧ ∀ p : K,
      (∀ k, b ≤ physicalWeight d (profile hd0 hdU ⟨p.val,hpos p.property⟩) k) ∧
      ‖profile hd0 hdU ⟨p.val,hpos p.property⟩‖ ≤ C := by
  letI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let f : K → positiveDomain d := fun p => ⟨p.val,hpos p.property⟩
  have hf : Continuous f := continuous_subtype_val.subtype_mk _
  have hw : Continuous (fun q : K × FourCircle => physicalWeight d (profile hd0 hdU (f q.1)) q.2) :=
    (physicalWeight_joint_continuous hd0 hdU).comp ((hf.comp continuous_fst).prodMk continuous_snd)
  obtain ⟨b,hb,hbmin⟩ := (isCompact_univ : IsCompact (univ : Set (K × FourCircle))).exists_forall_le'
    hw.continuousOn (fun q _ => physicalWeight_positive hd0 hdU (profile hd0 hdU (f q.1))
      (profile_positive hd0 hdU (f q.1)) q.2)
  have hn : Continuous (fun p : K => ‖profile hd0 hdU (f p)‖+1) :=
    ((profile_continuous hd0 hdU).comp hf).norm.add continuous_const
  by_cases hne : (univ : Set K).Nonempty
  · obtain ⟨p0,_,hmax⟩ := (isCompact_univ : IsCompact (univ : Set K)).exists_isMaxOn hne hn.continuousOn
    refine ⟨b,‖profile hd0 hdU (f p0)‖+1,hb,by positivity,fun p => ?_⟩
    refine ⟨fun k => hbmin (p,k) (mem_univ _),?_⟩
    have h := hmax (mem_univ p)
    change ‖profile hd0 hdU (f p)‖+1 ≤ ‖profile hd0 hdU (f p0)‖+1 at h
    linarith
  · exact ⟨b,1,hb,by norm_num,fun p => (hne ⟨p,mem_univ _⟩).elim⟩

end
end Resonance.PinnedRJProfile
