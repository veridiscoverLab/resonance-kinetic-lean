import Resonance.CompactFormStability

/-! Compression to one fixed microscopic subspace. The positive baseline
is required only there; the full collision space may retain all five zero
modes. No invariance of that subspace under the varying diagonal is assumed. -/
open Set Filter
open scoped InnerProductSpace Topology
namespace Resonance.CompactSubspaceStability
noncomputable section
variable {E I : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
set_option maxHeartbeats 1800000

local instance subspaceOpNorm (W : Submodule ℝ E) : Norm (W →L[ℝ] W) :=
  ContinuousLinearMap.hasOpNorm

def compress (W : Submodule ℝ E) [W.HasOrthogonalProjection]
    (A : E →L[ℝ] E) : W →L[ℝ] W :=
  W.orthogonalProjection.comp (A.comp W.subtypeL)

theorem compress_pairing (W : Submodule ℝ E) [W.HasOrthogonalProjection]
    (A : E →L[ℝ] E) (u v : W) :
    inner ℝ u (compress W A v) = inner ℝ (u:E) (A v) := by
  change inner ℝ (u:E) (W.starProjection (A v)) = _
  rw [←W.inner_starProjection_left_eq_right]
  rw [W.starProjection_eq_self_iff.mpr u.property]

theorem compress_bound (W : Submodule ℝ E) [W.HasOrthogonalProjection]
    (A : E →L[ℝ] E) : ‖compress W A‖ ≤ ‖A‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro u
  change ‖W.starProjection (A u)‖ ≤ ‖A‖*‖u‖
  exact (W.norm_starProjection_apply_le _).trans (A.le_opNorm u)

theorem compress_compact (W : Submodule ℝ E) [W.HasOrthogonalProjection]
    (K : E →L[ℝ] E) (hK : IsCompactOperator K) :
    IsCompactOperator (compress W K) :=
  (hK.comp_clm W.subtypeL).clm_comp W.orthogonalProjection

/-- The same fixed subspace is used at every index. Compression is part of
the proof, not an invariance assumption for A or V. -/
theorem eventual_micro_coercivity (W : Submodule ℝ E) [W.HasOrthogonalProjection]
    (K : E →L[ℝ] E) (hKc : IsCompactOperator K)
    (hKs : ∀x y, inner ℝ (K x) y = inner ℝ x (K y))
    (A V : I → E →L[ℝ] E) (l : Filter I) {a c B : ℝ}
    (ha : 0 < a) (hc : 0 < c) (hB : 0 ≤ B)
    (hAs : ∀i x y, inner ℝ (A i x) y = inner ℝ x (A i y))
    (hlower : ∀i x, a*‖x‖^2 ≤ inner ℝ x (A i x))
    (hbase : ∀x∈W, c*‖x‖^2 ≤ ‖x‖^2+inner ℝ x (K x))
    (hbound : ∀ᶠi in l, ‖A i‖ ≤ B)
    (hstrong : ∀x, Tendsto (fun i=>A i x) l (𝓝 x))
    (hV : Tendsto (fun i=>‖V i‖) l (𝓝 0)) :
    ∀ᶠi in l, ∀u∈W, (min a c/4)*‖u‖^2 ≤ inner ℝ u ((A i+K+V i) u) := by
  have hcs : ∀x y:W, inner ℝ (compress W K x) y = inner ℝ x (compress W K y) := by
    intro x y
    rw [real_inner_comm,compress_pairing,←hKs,real_inner_comm,compress_pairing]
  have has : ∀i (x y:W), inner ℝ (compress W (A i) x) y =
      inner ℝ x (compress W (A i) y) := by
    intro i x y
    rw [real_inner_comm,compress_pairing,←hAs,real_inner_comm,compress_pairing]
  have hal : ∀i (x:W), a*‖x‖^2 ≤ inner ℝ x (compress W (A i) x) := by
    intro i x
    rw [compress_pairing]
    exact hlower i x
  have hbl : ∀x:W, c*‖x‖^2 ≤ ‖x‖^2+inner ℝ x (compress W K x) := by
    intro x
    rw [compress_pairing]
    exact hbase x x.property
  have hab : ∀ᶠi in l, ‖compress W (A i)‖ ≤ B := by
    filter_upwards [hbound] with i hi
    exact (compress_bound W _).trans hi
  have hat : ∀x:W, Tendsto (fun i=>compress W (A i) x) l (𝓝 x) := by
    intro x
    have hh:=W.orthogonalProjection.continuous.tendsto (x:E)
    have hx : W.orthogonalProjection (x:E) = x := by
      apply Subtype.ext
      exact W.starProjection_eq_self_iff.mpr x.property
    rw [hx] at hh
    exact hh.comp (hstrong x)
  have hvt : Tendsto (fun i=>‖compress W (V i)‖) l (𝓝 0) :=
    squeeze_zero (fun i=>(compress W (V i)).opNorm_nonneg) (fun i=>compress_bound W (V i)) hV
  have hh:=CompactFormStability.eventual_perturbed_coercivity
    (compress W K) (compress_compact W K hKc) hcs
    (fun i=>compress W (A i)) (fun i=>compress W (V i)) l ha hc hB
    has hal hbl hab hat hvt
  filter_upwards [hh] with i hi
  intro u hu
  have hu' := hi (⟨u,hu⟩:W)
  change (min a c/4)*‖(⟨u,hu⟩:W)‖^2 ≤ inner ℝ (⟨u,hu⟩:W)
    (compress W (A i) ⟨u,hu⟩+compress W K ⟨u,hu⟩+compress W (V i) ⟨u,hu⟩) at hu'
  rw [inner_add_right,inner_add_right,compress_pairing,compress_pairing,compress_pairing] at hu'
  simp only [ContinuousLinearMap.add_apply,inner_add_right]
  exact hu'

end
end Resonance.CompactSubspaceStability
