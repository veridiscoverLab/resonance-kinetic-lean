import Resonance.CoordinateReplacementControl
import Mathlib.Topology.Algebra.Support

/-! Compactly supported amplitudes transported through a genuine partial
homeomorphism. The inverse outside its target is never treated as continuous. -/
open Set Filter
open scoped Topology
namespace Resonance.ChartedCompactSupport
noncomputable section
open PinnedMeasure
variable {E : Type*} [TopologicalSpace E] [Zero E]

def transport (e : OpenPartialHomeomorph Ambient Ambient) (F : Ambient → E)
    (y : Ambient) : E := e.target.indicator (fun q => F (e.symm q)) y

omit [TopologicalSpace E] in
theorem transport_support_subset (e : OpenPartialHomeomorph Ambient Ambient)
    (F : Ambient → E) : Function.support (transport e F) ⊆ e '' tsupport F := by
  intro y hy
  have hyt : y∈e.target := by
    by_contra ht
    exact hy (by simp [transport, ht])
  have hF : F (e.symm y)≠0 := by
    simpa [transport, hyt] using hy
  exact ⟨e.symm y, subset_tsupport F hF, e.right_inv hyt⟩

omit [TopologicalSpace E] in
theorem transported_compact_support (e : OpenPartialHomeomorph Ambient Ambient)
    {F : Ambient → E} (hK : HasCompactSupport F) (hsub : tsupport F⊆e.source) :
    HasCompactSupport (transport e F) := by
  have hKi : IsCompact (e '' tsupport F) := hK.image_of_continuousOn (e.continuousOn.mono hsub)
  exact hKi.of_isClosed_subset (isClosed_tsupport _)
    (closure_minimal (transport_support_subset e F) hKi.isClosed)

theorem transported_continuous (e : OpenPartialHomeomorph Ambient Ambient)
    {F : Ambient → E} (hF : ContinuousOn F e.source)
    (hK : HasCompactSupport F) (hsub : tsupport F⊆e.source) :
    Continuous (transport e F) := by
  have hKi : IsCompact (e '' tsupport F) := hK.image_of_continuousOn (e.continuousOn.mono hsub)
  apply continuous_iff_continuousAt.mpr
  intro y
  by_cases hy : y∈e.target
  · have hc : ContinuousAt (fun q => F (e.symm q)) y :=
      (hF.continuousAt (e.open_source.mem_nhds (e.map_target hy))).comp
        (e.symm.continuousAt hy)
    apply hc.congr
    filter_upwards [e.open_target.mem_nhds hy] with q hq
    simp [transport, hq]
  · have hyK : y∉e '' tsupport F := by
      rintro ⟨x,hx,rfl⟩
      exact hy (e.map_source (hsub hx))
    have hz : (fun _ : Ambient => (0:E)) =ᶠ[𝓝 y] transport e F := by
      filter_upwards [hKi.isClosed.isOpen_compl.mem_nhds hyK] with q hq
      apply Eq.symm
      by_contra hs
      exact hq (transport_support_subset e F hs)
    exact continuousAt_const.congr hz

end
end Resonance.ChartedCompactSupport
