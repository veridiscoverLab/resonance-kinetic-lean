import Resonance.Thermodynamics

/-!
A genuine C¹ thermodynamic chart for the manuscript's five-moment map on its
entire positive Rayleigh--Jeans parameter domain.  The derivative equivalence,
the inverse, and openness of the moment image are constructed from the actual
sharp-cube integral, not assumed.  No assertion here concerns a PDE solution
or quantitative bounds uniform over a prescribed Euler trajectory.
-/

open MeasureTheory
open scoped BigOperators

namespace Resonance.ThermodynamicChart

open Resonance.Entropy Resonance.Thermodynamics

/-- The actual differential, promoted to an equivalence using its proved
injectivity and the equal finite dimensions of the parameter and moment spaces. -/
noncomputable def derivativeEquiv (R : ℝ) (hR : 0 < R) (θ : Parameter)
    (hθ : θ ∈ positiveDomain R) : Parameter ≃L[ℝ] Parameter :=
  (LinearEquiv.ofBijective (momentDerivative R θ).toLinearMap
    ⟨momentDerivative_injective R hR θ hθ,
      LinearMap.injective_iff_surjective.mp (momentDerivative_injective R hR θ hθ)⟩
      ).toContinuousLinearEquiv

theorem derivativeEquiv_toCLM (R : ℝ) (hR : 0 < R) (θ : Parameter)
    (hθ : θ ∈ positiveDomain R) :
    (derivativeEquiv R hR θ hθ : Parameter →L[ℝ] Parameter) =
      momentDerivative R θ := by
  ext b
  rfl

theorem momentMap_contDiffAt (R : ℝ) (θ : Parameter)
    (hθ : θ ∈ positiveDomain R) :
    ContDiffAt ℝ 1 (momentMap R) θ :=
  (momentMap_contDiffOn_one R).contDiffAt ((positiveDomain_isOpen R).mem_nhds hθ)

theorem momentMap_hasFDerivAt_equiv (R : ℝ) (hR : 0 < R) (θ : Parameter)
    (hθ : θ ∈ positiveDomain R) :
    HasFDerivAt (momentMap R)
      (derivativeEquiv R hR θ hθ : Parameter →L[ℝ] Parameter) θ := by
  rw [derivativeEquiv_toCLM]
  exact momentMap_hasFDerivAt R θ hθ

theorem momentMap_hasStrictFDerivAt (R : ℝ) (hR : 0 < R) (θ : Parameter)
    (hθ : θ ∈ positiveDomain R) :
    HasStrictFDerivAt (momentMap R)
      (derivativeEquiv R hR θ hθ : Parameter →L[ℝ] Parameter) θ :=
  (momentMap_contDiffAt R θ hθ).hasStrictFDerivAt'
    (momentMap_hasFDerivAt_equiv R hR θ hθ) (by norm_num)

/-- The inverse-function theorem is applied at every actual positive parameter. -/
theorem momentMap_map_nhds (R : ℝ) (hR : 0 < R) (θ : Parameter)
    (hθ : θ ∈ positiveDomain R) :
    Filter.map (momentMap R) (nhds θ) = nhds (momentMap R θ) :=
  (momentMap_hasStrictFDerivAt R hR θ hθ).map_nhds_eq_of_equiv

theorem restrictedMomentMap_isOpenMap (R : ℝ) (hR : 0 < R) :
    IsOpenMap ((positiveDomain R).restrict (momentMap R)) := by
  rw [isOpenMap_iff_nhds_le]
  intro θ
  have he : Filter.map ((positiveDomain R).restrict (momentMap R)) (nhds θ) =
      nhds (momentMap R θ) := by
    change Filter.map (momentMap R ∘ Subtype.val) (nhds θ) = _
    rw [← Filter.map_map,
      (positiveDomain_isOpen R).isOpenEmbedding_subtypeVal.map_nhds_eq,
      momentMap_map_nhds R hR θ θ.property]
  exact he.ge

def momentImage (R : ℝ) : Set Parameter := momentMap R '' positiveDomain R

theorem momentImage_isOpen (R : ℝ) (hR : 0 < R) : IsOpen (momentImage R) := by
  simpa only [Set.range_restrict, momentImage] using
    (restrictedMomentMap_isOpenMap R hR).isOpen_range

/-- One global chart: its source is the full positive parameter domain, and its
target is precisely the moment image.  The inverse is provided by the actual
injectivity and the inverse-function theorem, not by a parameter hypothesis. -/
noncomputable def momentChart (R : ℝ) (hR : 0 < R) :
    OpenPartialHomeomorph Parameter Parameter :=
  OpenPartialHomeomorph.ofContinuousOpenRestrict
    ((momentMap_injective R hR).toPartialEquiv (momentMap R) (positiveDomain R))
    (momentMap_contDiffOn_one R).continuousOn
    (restrictedMomentMap_isOpenMap R hR) (positiveDomain_isOpen R)

@[simp] theorem momentChart_source (R : ℝ) (hR : 0 < R) :
    (momentChart R hR).source = positiveDomain R := rfl

@[simp] theorem momentChart_target (R : ℝ) (hR : 0 < R) :
    (momentChart R hR).target = momentImage R := rfl

@[simp] theorem momentChart_apply (R : ℝ) (hR : 0 < R) (θ : Parameter) :
    momentChart R hR θ = momentMap R θ := rfl

noncomputable def momentInverse (R : ℝ) (hR : 0 < R) : Parameter → Parameter :=
  (momentChart R hR).symm

theorem momentInverse_mem (R : ℝ) (hR : 0 < R) (U : Parameter)
    (hU : U ∈ momentImage R) : momentInverse R hR U ∈ positiveDomain R :=
  (momentChart R hR).map_target hU

theorem momentInverse_left (R : ℝ) (hR : 0 < R) (θ : Parameter)
    (hθ : θ ∈ positiveDomain R) :
    momentInverse R hR (momentMap R θ) = θ :=
  (momentChart R hR).left_inv hθ

theorem momentInverse_right (R : ℝ) (hR : 0 < R) (U : Parameter)
    (hU : U ∈ momentImage R) :
    momentMap R (momentInverse R hR U) = U :=
  (momentChart R hR).right_inv hU

theorem momentInverse_contDiffAt (R : ℝ) (hR : 0 < R) (U : Parameter)
    (hU : U ∈ momentImage R) :
    ContDiffAt ℝ 1 (momentInverse R hR) U :=
  (momentChart R hR).contDiffAt_symm hU
    (momentMap_hasFDerivAt_equiv R hR (momentInverse R hR U)
      (momentInverse_mem R hR U hU))
    (momentMap_contDiffAt R (momentInverse R hR U)
      (momentInverse_mem R hR U hU))

theorem momentInverse_contDiffOn (R : ℝ) (hR : 0 < R) :
    ContDiffOn ℝ 1 (momentInverse R hR) (momentImage R) :=
  fun U hU => (momentInverse_contDiffAt R hR U hU).contDiffWithinAt

theorem momentInverse_hasFDerivAt (R : ℝ) (hR : 0 < R) (U : Parameter)
    (hU : U ∈ momentImage R) :
    HasFDerivAt (momentInverse R hR)
      ((derivativeEquiv R hR (momentInverse R hR U)
        (momentInverse_mem R hR U hU)).symm : Parameter →L[ℝ] Parameter) U :=
  (momentChart R hR).hasFDerivAt_symm hU
    (momentMap_hasFDerivAt_equiv R hR (momentInverse R hR U)
      (momentInverse_mem R hR U hU))

/-- The positive parameter domain is homeomorphic to its actual open moment image. -/
noncomputable def momentHomeomorph (R : ℝ) (hR : 0 < R) :
    positiveDomain R ≃ₜ momentImage R :=
  (momentChart R hR).toHomeomorphSourceTarget

@[simp] theorem momentHomeomorph_apply (R : ℝ) (hR : 0 < R)
    (θ : positiveDomain R) :
    (momentHomeomorph R hR θ : Parameter) = momentMap R θ := rfl

@[simp] theorem momentHomeomorph_symm_apply (R : ℝ) (hR : 0 < R)
    (U : momentImage R) :
    ((momentHomeomorph R hR).symm U : Parameter) = momentInverse R hR U := rfl


/-- The derivative of the inverse solves the original Gram equation
M(θ) Dθ(U)b = -b, where θ is the actual matched parameter. -/
theorem momentInverse_fderiv_gram (R : ℝ) (hR : 0 < R) (U : Parameter)
    (hU : U ∈ momentImage R) (b : Parameter) :
    (gramMatrix R (momentInverse R hR U)).mulVec
      (fderiv ℝ (momentInverse R hR) U b) = -b := by
  rw [(momentInverse_hasFDerivAt R hR U hU).fderiv]
  have he : momentDerivative R (momentInverse R hR U)
      ((derivativeEquiv R hR (momentInverse R hR U)
        (momentInverse_mem R hR U hU)).symm b) = b :=
    (derivativeEquiv R hR (momentInverse R hR U)
      (momentInverse_mem R hR U hU)).apply_symm_apply b
  rw [momentDerivative_apply R _ (momentInverse_mem R hR U hU)] at he
  simpa only [neg_neg] using congrArg (fun x : Parameter => -x) he

/-- Unique matching is asserted exactly on the open moment image. -/
theorem existsUnique_matched_parameter (R : ℝ) (hR : 0 < R) (U : Parameter)
    (hU : U ∈ momentImage R) :
    ∃! θ : Parameter, θ ∈ positiveDomain R ∧ momentMap R θ = U := by
  refine ⟨momentInverse R hR U,
    ⟨momentInverse_mem R hR U hU, momentInverse_right R hR U hU⟩, ?_⟩
  intro θ hθ
  apply momentMap_injective R hR hθ.1 (momentInverse_mem R hR U hU)
  exact hθ.2.trans (momentInverse_right R hR U hU).symm

end Resonance.ThermodynamicChart

