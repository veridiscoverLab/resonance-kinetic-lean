import Mathlib.Analysis.InnerProductSpace.Projection.Basic

/-! Distance to a closed kernel under an actual bounded invertible map.
The norm of the inverse is retained; the map is not assumed unitary. -/
open Set
namespace Resonance.HilbertPullbackDistance
noncomputable section
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem projection_residual_le (K : Submodule ℂ H) [CompleteSpace K]
    (f g : H) (hg : g∈K) : ‖f-K.starProjection f‖ ≤ ‖f-g‖ := by
  have h := Kᗮ.norm_starProjection_apply_le (f-g)
  rw [Submodule.starProjection_orthogonal',ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.one_apply,map_sub,K.starProjection_eq_self_iff.mpr hg] at h
  convert h using 1
  congr 1
  abel

theorem comap_isClosed (K : Submodule ℂ H) (hK : IsClosed (K : Set H))
    (U : H≃L[ℂ]H) : IsClosed (K.comap U.toLinearMap : Set H) :=
  hK.preimage U.continuous

theorem pullback_distance_bound (K : Submodule ℂ H) [CompleteSpace K]
    (U : H≃L[ℂ]H) [CompleteSpace (K.comap U.toLinearMap)]
    (C : ℝ) (hC : ∀v : H,‖U.symm v‖ ≤ C*‖v‖) (f : H) :
    ‖f-(K.comap U.toLinearMap).starProjection f‖ ≤ C*‖U f-K.starProjection (U f)‖ := by
  let p := U.symm (K.starProjection (U f))
  have hp : p∈K.comap U.toLinearMap := by
    change U (U.symm (K.starProjection (U f)))∈K
    rw [U.apply_symm_apply]
    exact K.starProjection_apply_mem (U f)
  calc
    _ ≤ ‖f-p‖ := projection_residual_le _ f p hp
    _ = ‖U.symm (U f-K.starProjection (U f))‖ := by rw [map_sub,U.symm_apply_apply]
    _ ≤ _ := hC _

end
end Resonance.HilbertPullbackDistance
