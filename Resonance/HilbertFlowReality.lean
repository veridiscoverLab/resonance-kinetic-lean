import Resonance.HilbertExponentialFlow
import Resonance.HilbertForwardODEEnergy

/-! Forward uniqueness for a bounded complex Hilbert generator and its
real-linear intertwining. No stability or real-subspace invariance is assumed. -/
open Set ContinuousLinearMap
namespace Resonance.HilbertFlowReality
noncomputable section
open HilbertQuadraticBounds HilbertForwardODEEnergy HilbertExponentialFlow
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

set_option backward.isDefEq.respectTransparency false in
theorem forward_zero_unique (G : E→L[ℂ]E) {u : ℝ→E} {T : ℝ} (hT : 0≤T)
    (hu : ∀s∈Icc 0 T,HasDerivWithinAt u (G (u s)) (Icc 0 T) s) (h0 : u 0=0) : u T=0 := by
  have hi : ∀v:E,quadratic (1:E→L[ℂ]E) v=‖v‖^2 := by
    intro v
    change (inner ℂ v v).re=‖v‖^2
    exact (norm_sq_eq_re_inner (𝕜:=ℂ) v).symm
  have hb : ∀s∈Icc 0 T,quadratic ((1:E→L[ℂ]E)*G+star G*1) (u s)≤
      -(-2*‖G‖)*quadratic (1:E→L[ℂ]E) (u s) := by
    intro s _
    have hh := (le_abs_self (quadratic (G+star G) (u s))).trans (abs_quadratic_bound (G+star G) (u s))
    have hn : ‖G+star G‖≤2*‖G‖ := by
      have hs : ‖star G‖=‖G‖ := ContinuousLinearMap.adjoint.norm_map G
      simpa only [hs,two_mul] using norm_add_le G (star G)
    have hm := mul_le_mul_of_nonneg_right hn (sq_nonneg ‖u s‖)
    simp only [one_mul,mul_one,hi]
    nlinarith
  have hd := scalar_forward_decay hT
    (fun s hs=>hasDerivWithinAt_quadratic (1:E→L[ℂ]E) G (hu s hs)) (-2*‖G‖) hb
  rw [hi,hi,h0,norm_zero] at hd
  have hz : ‖u T‖^2=0 := le_antisymm (by simpa using hd) (sq_nonneg _)
  exact norm_eq_zero.mp (sq_eq_zero_iff.mp hz)

set_option backward.isDefEq.respectTransparency false in
theorem flow_real_intertwining (F : E→L[ℝ]E) (G₁ G₂ : E→L[ℂ]E)
    (hFG : ∀v:E,F (G₁ v)=G₂ (F v)) (v : E) {t : ℝ} (ht : 0≤t) :
    F (flow G₁ t v)=flow G₂ t (F v) := by
  let u := fun s=>F (flow G₁ s v)-flow G₂ s (F v)
  have hu : ∀s∈Icc 0 t,HasDerivWithinAt u (G₂ (u s)) (Icc 0 t) s := by
    intro s _
    have h1 := F.hasFDerivAt.comp_hasDerivAt s (flow_hasDerivAt G₁ v s)
    have h2 := flow_hasDerivAt G₂ (F v) s
    have hh := h1.sub h2
    rw [hFG,←map_sub] at hh
    exact hh.hasDerivWithinAt
  have h0 : u 0=0 := by simp [u,flow_zero]
  exact sub_eq_zero.mp (forward_zero_unique G₂ ht hu h0)

end
end Resonance.HilbertFlowReality
