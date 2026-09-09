import Resonance.PinnedLocalCompleteLimit
import Resonance.FiniteCompactPartition
import Resonance.FiniteEventualSourceLimit

/-! The complete original compact-source delta theorem. The actual regular,
both critical, and off-energy neighborhoods are joined by a finite exact
partition of the same source, with the same arbitrary shrinking kernel. -/
open Set MeasureTheory Filter
open scoped ContDiff Topology
namespace Resonance.PinnedCompactCompleteLimit
noncomputable section
open PinnedMeasure PinnedPeriodicity PinnedCriticalCancellation PinnedMeasureNormalization
open PinnedLocalCompleteLimit

theorem compact_complete_source_limit {d : ℝ} (hd0 : 0<d) (hdU : d<1/2)
    {φ : ℝ → ℂ} (hφ : ContDiff ℝ 2 φ) (hp : Function.Periodic φ period)
    {W : Ambient → ℂ} (hW : Continuous W) (hK : HasCompactSupport W)
    (ρ : ℝ → ℝ → ℝ) (hm : ∀η,0<η→Measurable (ρ η))
    (hρ : ∀η,0<η→Integrable (ρ η)) (hpos : ∀η,0<η→∀q,0≤ρ η q)
    (hmass : ∀η,0<η→∫q,ρ η q=1)
    (hs : ∀η,0<η→∀q,ρ η q≠0→|q|≤η) :
    (∀ᶠη in 𝓝[>]0,Integrable (fun k=>ρ η (liftedEnergy d k) • (W k*fullDifference φ k))) ∧
    Integrable (fun k=>W k*fullDifference φ k) (euclideanLiftedRegularCoarea d) ∧
    Tendsto (fun η=>((2*Real.pi)^3)⁻¹ • ∫k,ρ η (liftedEnergy d k) • (W k*fullDifference φ k))
      (𝓝[>]0) (𝓝 (∫k,W k*fullDifference φ k ∂euclideanLiftedRegularCoarea d)) := by
  classical
  choose U hU hk hlocal using every_point_limit hd0 hdU hφ hp ρ hm hρ hpos hmass hs
  have hcover : tsupport W⊆⋃k,U k := fun k _=>mem_iUnion.mpr ⟨k,hk k⟩
  obtain ⟨I,ψ,_,_,hsum,hpieces⟩ := FiniteCompactPartition.finite_source_decomposition hW hK U hU hcover
  let Wi : (↑I) → Ambient → ℂ := fun i k=>ψ i k • W k
  have hlim : ∀i:↑I,SourceLimit d φ ρ (Wi i) := fun i=>
    hlocal i (Wi i) (hpieces i).1 (hpieces i).2.1 (hpieces i).2.2
  have heq : ∀k,∑i:↑I,Wi i k*fullDifference φ k=W k*fullDifference φ k := by
    intro k
    rw [←Finset.sum_mul]
    exact congrArg (fun z : ℂ=>z*fullDifference φ k) (hsum k)
  exact FiniteEventualSourceLimit.common_integral_limit volume (euclideanLiftedRegularCoarea d)
    (fun k=>W k*fullDifference φ k) (fun i k=>Wi i k*fullDifference φ k) heq
    (fun η k=>ρ η (liftedEnergy d k)) (((2*Real.pi)^3)⁻¹)
    (fun i=>(hlim i).1) (fun i=>(hlim i).2.1) (fun i=>(hlim i).2.2)

theorem compact_complete_form_limit {d : ℝ} (hd0 : 0<d) (hdU : d<1/2)
    {φ ψ : ℝ → ℂ} (hφ : ContDiff ℝ 2 φ) (hp : Function.Periodic φ period)
    (hψ : Continuous ψ) {W : Ambient → ℂ} (hW : Continuous W) (hK : HasCompactSupport W)
    (ρ : ℝ → ℝ → ℝ) (hm : ∀η,0<η→Measurable (ρ η))
    (hρ : ∀η,0<η→Integrable (ρ η)) (hpos : ∀η,0<η→∀q,0≤ρ η q)
    (hmass : ∀η,0<η→∫q,ρ η q=1)
    (hs : ∀η,0<η→∀q,ρ η q≠0→|q|≤η) :
    SourceLimit d φ ρ (fun k=>W k*star (fullDifference ψ k)) := by
  exact compact_complete_source_limit hd0 hdU hφ hp
    (hW.mul (fullDifference_continuous hψ).star) hK.mul_right ρ hm hρ hpos hmass hs

end
end Resonance.PinnedCompactCompleteLimit
