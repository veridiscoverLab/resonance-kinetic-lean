import Resonance.PhysicalFrequencyBounds
import Resonance.GramGapCoordinateTransfer

/-! The complete collision form in the manuscript's fixed physical
space L2(D,nu_* dk), with actual h=u/N and uniform positive-parameter
coercivity. -/
open MeasureTheory Set
namespace Resonance.PhysicalWeightedCoercivity
noncomputable section
open ResonantMeasure WeightedJointMeasure Thermodynamics FrequencyWeightedForm
open ReferenceFrequencySpace PhysicalFrequencyCoordinates PhysicalFrequencyBounds
open JointWeightComparison ReferenceMarginalTransport

def physicalForm {R : ℝ} (hR : 0≤R) {θ : Parameter} (hθ : θ∈positiveDomain R)
    (u v : Space R) : ℝ := inner ℝ (physicalDifference hR hθ u) (physicalDifference hR hθ v)

theorem physical_form_integrable {R : ℝ} (hR : 0≤R) {θ : Parameter}
    (hθ : θ∈positiveDomain R) (u v : Space R) :
    Integrable (fun q=>CollisionForm.rawDifference (fun k=>u k/profile θ k) q*
      CollisionForm.rawDifference (fun k=>v k/profile θ k) q) (jointMeasure R θ) := by
  apply (L2.integrable_inner (physicalDifference hR hθ v) (physicalDifference hR hθ u)).congr
  filter_upwards [physicalDifference_ae hR hθ u,physicalDifference_ae hR hθ v] with q hu hv
  change physicalDifference hR hθ u q*physicalDifference hR hθ v q=_
  rw [hu,hv]

theorem physical_form_integral {R : ℝ} (hR : 0≤R) {θ : Parameter}
    (hθ : θ∈positiveDomain R) (u v : Space R) :
    physicalForm hR hθ u v=∫q,CollisionForm.rawDifference (fun k=>u k/profile θ k) q*
      CollisionForm.rawDifference (fun k=>v k/profile θ k) q∂jointMeasure R θ := by
  rw [physicalForm,L2.inner_def]
  apply integral_congr_ae
  filter_upwards [physicalDifference_ae hR hθ u,physicalDifference_ae hR hθ v] with q hu hv
  change physicalDifference hR hθ v q*physicalDifference hR hθ u q=_
  rw [hu,hv,mul_comm]

theorem physical_form_square {R : ℝ} (hR : 0≤R) {θ : Parameter}
    (hθ : θ∈positiveDomain R) (u : Space R) :
    physicalForm hR hθ u u=‖physicalDifference hR hθ u‖^2 :=
  real_inner_self_eq_norm_sq _

theorem physical_kernel_classification {R : ℝ} (hR : 0<R) {θ : Parameter}
    (hθ : θ∈positiveDomain R) (u : Space R) :
    u∈(physicalDifference hR.le hθ).ker ↔
      ∃!b : QuadraticPointwiseClosure.Coefficients,
        (u : E→ℝ)=ᵐ[volume.restrict (cube R)]
          (fun k=>profile θ k*QuadraticPointwiseClosure.evaluate b k) := by
  have hf : (forward hR.le hθ u : E→ℝ)=ᵐ[volume.restrict (cube R)]
      (fun k=>u k/profile θ k) :=
    (ActualPairNormalization.cube_marginal_equivalent hR hθ).1.ae_eq (forward_ae hR.le hθ u)
  have hrel (b : QuadraticPointwiseClosure.Coefficients) :
      ((forward hR.le hθ u : E→ℝ)=ᵐ[volume.restrict (cube R)] QuadraticPointwiseClosure.evaluate b) ↔
      ((u : E→ℝ)=ᵐ[volume.restrict (cube R)]
        (fun k=>profile θ k*QuadraticPointwiseClosure.evaluate b k)) := by
    constructor
    · intro hb
      filter_upwards [hb,hf,ae_restrict_mem (measurable_cube R)] with k hk hfk hkc
      rw [hfk] at hk
      exact ((div_eq_iff (profile_pos hθ hkc).ne').mp hk).trans (mul_comm _ _)
    · intro hb
      filter_upwards [hb,hf,ae_restrict_mem (measurable_cube R)] with k hk hfk hkc
      rw [hfk]
      exact (div_eq_iff (profile_pos hθ hkc).ne').mpr (hk.trans (mul_comm _ _))
  change forward hR.le hθ u∈(fullDifference R θ).ker ↔_
  rw [ActualWeightedCoercivity.actual_kernel_classification hR hθ]
  exact existsUnique_congr hrel

theorem physical_uniform_coercivity {R : ℝ} (hR : 0<R) {K : Set Parameter}
    (hK : IsCompact K) (hpos : K⊆positiveDomain R) :
    ∃δ : ℝ,0<δ ∧ ∀θ,(hθ : θ∈K) → ∀u : Space R,
      δ*‖u-(physicalDifference hR.le (hpos hθ)).ker.starProjection u‖^2≤
        physicalForm hR.le (hpos hθ) u u := by
  obtain ⟨m,M,hm,hM,hbounds⟩ := compact_profile_bounds hR.le hK hpos
  obtain ⟨δ,hδ,hgap⟩ := UniformWeightedCoercivity.profile_bounded_uniform_coercivity (M:=M) hR hm
  let a : ℝ := M*LpOperators.changeNorm (toReferenceFactor R m)
  have hd : 0<δ/(1+a^2) := div_pos hδ (by positivity)
  refine ⟨δ/(1+a^2),hd,?_⟩
  intro θ hθ u
  have hh := GramGapCoordinateTransfer.transfer_square_gap (fullDifference R θ)
    (forward hR.le (hpos hθ)) (backward hR.le (hpos hθ)) hδ.le
    (backward_uniform_bound hR.le hm hM.le (hpos hθ) (hbounds θ hθ))
    (backward_forward hR.le (hpos hθ)) (forward_backward hR.le (hpos hθ))
    (hgap θ (hpos hθ) (hbounds θ hθ)) u
  rw [physical_form_square]
  exact hh

end
end Resonance.PhysicalWeightedCoercivity
