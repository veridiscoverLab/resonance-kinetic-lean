import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Slope

/-! Smoothness is inherited by a complete isometric linear subspace.
The derivative is proved to lie in the actual closed range by genuine
difference quotients. This permits lifting an already smooth supremum
family without replacing its norm by coordinatewise regularity. -/
open Set Filter
open scoped Topology ContDiff
namespace Resonance.IsometricRangeSmooth
noncomputable section
set_option maxHeartbeats 1500000
universe u
variable {E F G : Type u}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

theorem derivative_mem_range [CompleteSpace F] (J : F→ₗᵢ[ℝ]G)
    {f : E→F} {x : E} {D : E→L[ℝ]G}
    (h : HasFDerivAt (fun y => J (f y)) D x) (v : E) : D v∈J.range := by
  let l : ℝ→L[ℝ]E := (ContinuousLinearMap.id ℝ ℝ).smulRight v
  have hl : HasFDerivAt (fun t : ℝ=>x+t•v) l 0 :=
    l.hasFDerivAt.const_add x
  have hd : HasDerivAt (fun t : ℝ => J (f (x+t•v))) (D v) 0 := by
    have hh : HasFDerivAt (fun y => J (f y)) D (x+(0 : ℝ)•v) := by simpa using h
    simpa [l] using (hh.comp 0 hl).hasDerivAt
  apply J.isometry.isClosedEmbedding.isClosed_range.mem_of_tendsto hd.tendsto_slope_zero
  filter_upwards [] with t
  change t⁻¹ • (J (f (x+(0+t)•v))-J (f (x+0•v)))∈Set.range J
  exact ⟨t⁻¹ • (f (x+(0+t)•v)-f (x+0•v)),by simp⟩

theorem hasFDerivAt_of_comp (J : F→ₗᵢ[ℝ]G)
    {f : E→F} {x : E} {D : E→L[ℝ]F}
    (h : HasFDerivAt (fun y => J (f y)) (J.toContinuousLinearMap.comp D) x) :
    HasFDerivAt f D x := by
  apply hasFDerivAt_iff_isLittleO.mpr
  apply Asymptotics.IsLittleO.of_norm_left
  convert (hasFDerivAt_iff_isLittleO.mp h).norm_left using 1
  funext y
  rw [←J.norm_map (f y-f x-D (y-x))]
  simp

theorem differentiableAt_of_comp [CompleteSpace F] (J : F→ₗᵢ[ℝ]G)
    {f : E→F} {x : E} (h : DifferentiableAt ℝ (fun y => J (f y)) x) :
    DifferentiableAt ℝ f x := by
  let D := fderiv ℝ (fun y => J (f y)) x
  let A : E→L[ℝ]F := J.equivRange.symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
    (D.codRestrict J.range (derivative_mem_range J h.hasFDerivAt))
  refine ⟨A,hasFDerivAt_of_comp J ?_⟩
  have he : J.toContinuousLinearMap.comp A=D := by
    apply ContinuousLinearMap.ext
    intro v
    exact congrArg Subtype.val (J.equivRange.apply_symm_apply
      ⟨D v,derivative_mem_range J h.hasFDerivAt v⟩)
  rw [he]
  exact h.hasFDerivAt

def operatorEmbed (J : F→ₗᵢ[ℝ]G) : (E→L[ℝ]F)→ₗᵢ[ℝ](E→L[ℝ]G) where
  toLinearMap :=
    { toFun := fun A=>J.toContinuousLinearMap.comp A
      map_add' := fun A B => by ext v; simp
      map_smul' := fun c A => by ext v; simp }
  norm_map' A := by
    apply le_antisymm
    · apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg A)
      intro v
      simpa using A.le_opNorm v
    · apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
      intro v
      simpa using (J.toContinuousLinearMap.comp A).le_opNorm v

theorem fderiv_comp [CompleteSpace F] (J : F→ₗᵢ[ℝ]G)
    {f : E→F} {x : E} (h : DifferentiableAt ℝ (fun y => J (f y)) x) :
    operatorEmbed J (fderiv ℝ f x)=fderiv ℝ (fun y => J (f y)) x := by
  exact ((J.toContinuousLinearMap.hasFDerivAt).comp x
    (differentiableAt_of_comp J h).hasFDerivAt).fderiv.symm

theorem contDiffOn_nat_of_comp [CompleteSpace F] (J : F→ₗᵢ[ℝ]G)
    (n : ℕ) {s : Set E} (hs : IsOpen s) {f : E→F}
    (h : ContDiffOn ℝ n (fun y => J (f y)) s) : ContDiffOn ℝ n f s := by
  induction n generalizing F G with
  | zero =>
    exact contDiffOn_zero.mpr
      (J.isometry.isEmbedding.isInducing.continuousOn_iff.mpr (contDiffOn_zero.mp h))
  | succ n ih =>
    have he : ((n+1 : ℕ) : WithTop ℕ∞) = (n : WithTop ℕ∞)+1 := by simp
    rw [he,contDiffOn_succ_iff_fderiv_of_isOpen hs] at h ⊢
    refine ⟨fun x hx => (differentiableAt_of_comp J
      ((h.1 x hx).differentiableAt (hs.mem_nhds hx))).differentiableWithinAt,
      by simp,?_⟩
    apply ih (operatorEmbed J)
    apply h.2.2.congr
    intro x hx
    exact fderiv_comp J ((h.1 x hx).differentiableAt (hs.mem_nhds hx))

theorem contDiffOn_infty_of_comp [CompleteSpace F] (J : F→ₗᵢ[ℝ]G)
    {s : Set E} (hs : IsOpen s) {f : E→F}
    (h : ContDiffOn ℝ ∞ (fun y => J (f y)) s) : ContDiffOn ℝ ∞ f s := by
  rw [contDiffOn_infty] at h ⊢
  exact fun n => contDiffOn_nat_of_comp J n hs (h n)

end
end Resonance.IsometricRangeSmooth
