import Resonance.ActualOnsagerContinuity
import Resonance.EffectiveOnsagerResponse

/-! Compact-parameter bounds for the actual response on its exact quotient.
The cell, tensor, and their parameter continuity are constructed upstream. -/
open Set
namespace Resonance.UniformOnsagerResponse
noncomputable section
set_option maxHeartbeats 800000
open Thermodynamics ActualOnsagerTensor ActualOnsagerPositive ActualOnsagerMatrix
open EffectiveGradientSpace EffectiveOnsagerResponse ActualOnsagerContinuity

theorem actual_effective_unit_bounds {R : ℝ} (hR : 0 < R) {K : Set Parameter}
    (hK : IsCompact K) (hpos : K ⊆ positiveDomain R) :
    ∃a A : ℝ,0 < a ∧ 0 < A ∧ ∀θ : K,∀p∈Metric.sphere (0 : Fin 8→ℝ) 1,
      a ≤ quadraticResponse hR (hpos θ.property) (reconstruction p) ∧
      quadraticResponse hR (hpos θ.property) (reconstruction p) ≤ A := by
  letI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let V := fun p : K×(Fin 8→ℝ)=>
    quadraticResponse hR (hpos p.1.property) (reconstruction p.2)
  have hpmap : Continuous (fun θ : K=>(⟨θ.val,hpos θ.property⟩ : positiveDomain R)) :=
    continuous_subtype_val.subtype_mk _
  have hc : Continuous V := actual_quadratic_joint_continuous hR |>.comp
    ((hpmap.comp continuous_fst).prodMk (reconstruction_continuous.comp continuous_snd))
  let S := (univ : Set K)×ˢMetric.sphere (0 : Fin 8→ℝ) 1
  have hs : IsCompact S := isCompact_univ.prod (isCompact_sphere (0 : Fin 8→ℝ) 1)
  have hp : ∀p∈S,0 < V p := by
    intro p hp
    apply effective_response_positive
    intro hz
    simpa [hz] using hp.2
  by_cases hn : S.Nonempty
  · obtain ⟨p,hp0,hmin⟩ := hs.exists_isMinOn hn hc.continuousOn
    obtain ⟨q,hq0,hmax⟩ := hs.exists_isMaxOn hn hc.continuousOn
    refine ⟨V p,V q,hp p hp0,hp q hq0,?_⟩
    intro θ w hw
    change V p ≤ V (θ,w) ∧ V (θ,w) ≤ V q
    exact ⟨@hmin (θ,w) ⟨mem_univ _,hw⟩,@hmax (θ,w) ⟨mem_univ _,hw⟩⟩
  · refine ⟨1,1,by norm_num,by norm_num,?_⟩
    intro θ w hw
    exact (hn ⟨(θ,w),mem_univ _,hw⟩).elim

theorem actual_effective_bounds {R : ℝ} (hR : 0 < R) {K : Set Parameter}
    (hK : IsCompact K) (hpos : K ⊆ positiveDomain R) :
    ∃a A : ℝ,0 < a ∧ 0 < A ∧ ∀θ : K,∀p : Fin 8→ℝ,
      a*‖p‖^2 ≤ quadraticResponse hR (hpos θ.property) (reconstruction p) ∧
      quadraticResponse hR (hpos θ.property) (reconstruction p) ≤ A*‖p‖^2 := by
  obtain ⟨a,A,ha,hA,hb⟩ := actual_effective_unit_bounds hR hK hpos
  refine ⟨a,A,ha,hA,?_⟩
  intro θ p
  by_cases hz : p=0
  · subst p
    rw [(effective_response_zero_iff hR (hpos θ.property) 0).mpr rfl]
    simp
  have hn : 0 < ‖p‖ := norm_pos_iff.mpr hz
  let w : Fin 8→ℝ := ‖p‖⁻¹ • p
  have hw : w∈Metric.sphere (0 : Fin 8→ℝ) 1 := by
    simp [w,norm_smul,hn.ne']
  have he : p=‖p‖ • w := by simp [w,smul_smul,hn.ne']
  have hb0 := hb θ w hw
  have hq : quadraticResponse hR (hpos θ.property) (reconstruction p)=
      ‖p‖^2*quadraticResponse hR (hpos θ.property) (reconstruction w) := by
    conv_lhs => rw [he]
    rw [reconstruction_smul,quadratic_smul]
  rw [hq]
  constructor <;> nlinarith [sq_nonneg ‖p‖]

theorem actual_quotient_bounds {R : ℝ} (hR : 0 < R) {K : Set Parameter}
    (hK : IsCompact K) (hpos : K ⊆ positiveDomain R) :
    ∃a A : ℝ,0 < a ∧ 0 < A ∧ ∀θ : K,∀ξ : Index→ℝ,
      a*‖observation ξ‖^2 ≤ quadraticResponse hR (hpos θ.property) ξ ∧
      quadraticResponse hR (hpos θ.property) ξ ≤ A*‖observation ξ‖^2 := by
  obtain ⟨a,A,ha,hA,hb⟩ := actual_effective_bounds hR hK hpos
  refine ⟨a,A,ha,hA,?_⟩
  intro θ ξ
  rw [actual_effective_response hR (hpos θ.property) ξ]
  exact hb θ (observation ξ)

end
end Resonance.UniformOnsagerResponse
