import Resonance.RegularizedCellBounds

/-! Uniqueness for the actual original bounded resolvent, using the full
collision square and the actual unweighted L2 term. No spectral gap or
moment restriction is required for this uniqueness argument. -/
open MeasureTheory Set
open scoped ENNReal
namespace Resonance.BoundedResolventUniqueness
noncomputable section
set_option maxHeartbeats 1400000
open ResonantMeasure Thermodynamics ReferenceFrequencySpace ActualPairNormalization
open PhysicalWeightedCoercivity ReferenceMomentFunctionals

theorem bounded_square_integrable {R : ℝ} (hR : 0<R) (u : Space R)
    (hu : MemLp (u : E→ℝ) ∞ (referenceMeasure R)) :
    Integrable (fun k=>(u k)^2) (cubeVolume R) := by
  simpa only [pow_two] using weighted_moment_integrable hR hu u

theorem square_zero_imp_zero {R : ℝ} (hR : 0<R) (u : Space R)
    (hu : MemLp (u : E→ℝ) ∞ (referenceMeasure R))
    (hz : (∫k,(u k)^2∂cubeVolume R)=0) : u=0 := by
  have hae : (fun k=>(u k)^2)=ᵐ[cubeVolume R] 0 :=
    (integral_eq_zero_iff_of_nonneg_ae (ae_of_all _ (fun _=>sq_nonneg _))
      (bounded_square_integrable hR u hu)).mp hz
  apply Lp.ext
  filter_upwards [(reference_volume_equivalent hR).2.ae_eq hae,
    Lp.coeFn_zero ℝ 2 (referenceMeasure R)] with k hk hz0
  simp only [Pi.zero_apply] at hk hz0
  rw [hz0]
  exact sq_eq_zero_iff.mp hk

theorem actual_bounded_resolvent_unique {R : ℝ} (hR : 0<R) {θ : Parameter}
    (hθ : θ∈positiveDomain R) {s : ℝ} (hs : 0 ≤ s) (u w : Space R)
    (hu : MemLp (u : E→ℝ) ∞ (referenceMeasure R))
    (hw : MemLp (w : E→ℝ) ∞ (referenceMeasure R))
    (he : ∀v : Space R,s*physicalForm hR.le hθ u v+(∫k,v k*u k∂cubeVolume R)=
      s*physicalForm hR.le hθ w v+(∫k,v k*w k∂cubeVolume R)) : u=w := by
  have hd : MemLp ((u-w : Space R) : E→ℝ) ∞ (referenceMeasure R) :=
    (memLp_congr_ae (Lp.coeFn_sub u w)).mpr (hu.sub hw)
  have hsubl : physicalForm hR.le hθ (u-w) (u-w)=
      physicalForm hR.le hθ u (u-w)-physicalForm hR.le hθ w (u-w) := by
    unfold physicalForm
    rw [map_sub,inner_sub_left]
  have hi : (∫k,((u-w : Space R) k)^2∂cubeVolume R)=
      (∫k,(u-w : Space R) k*u k∂cubeVolume R)-
        (∫k,(u-w : Space R) k*w k∂cubeVolume R) := by
    rw [←integral_sub (weighted_moment_integrable hR hu (u-w))
      (weighted_moment_integrable hR hw (u-w))]
    apply integral_congr_ae
    filter_upwards [(reference_volume_equivalent hR).1.ae_eq (Lp.coeFn_sub u w)] with k hk
    simp only [Pi.sub_apply] at hk
    rw [hk]
    ring
  have hp := he (u-w)
  have hs0 : 0≤physicalForm hR.le hθ (u-w) (u-w) := by
    rw [physical_form_square]
    positivity
  have he0 : (∫k,((u-w : Space R) k)^2∂cubeVolume R)=0 := by
    have hn : 0≤∫k,((u-w : Space R) k)^2∂cubeVolume R :=
      integral_nonneg (fun _=>sq_nonneg _)
    nlinarith
  exact sub_eq_zero.mp (square_zero_imp_zero hR (u-w) hd he0)

end
end Resonance.BoundedResolventUniqueness
