import Resonance.PinnedCriticalQCutoff
import Resonance.PinnedCriticalVAmplitude
import Resonance.ControlledCoordinateChart

/-! The actual critical classification constructs neighborhoods on which all
partial and denominator conditions of the two integral charts hold. -/
open Set
open scoped ContDiff Topology
namespace Resonance.PinnedControlledCritical
noncomputable section
open PinnedMeasure PinnedCriticalFactor PinnedCriticalNormalization PinnedCriticalCoordinates
open PinnedCriticalCancellation PinnedCriticalGauge CoordinateReplacement

theorem v_partial_at_zero {d : ℝ} (hd0 : 0<d) (hdU : d<1/2)
    {p : Ambient} (hv : p 2=0) :
    (fderiv ℝ (PinnedCriticalVAmplitude.coordinateFunction d) p) (unit 2)=sharedFactor d p := by
  have hd := (coordinateProjection 2).hasFDerivAt.mul
    ((sharedFactor_contDiff_one hd0 hdU).differentiable (by norm_num) p).hasFDerivAt
  change HasFDerivAt (PinnedCriticalVAmplitude.coordinateFunction d)
    (p 2 • fderiv ℝ (sharedFactor d) p + sharedFactor d p • coordinateProjection 2) p at hd
  rw [hd.fderiv]
  simp [hv,coordinateProjection,CoordinateReplacement.unit]

theorem every_critical_point_controlled {d : ℝ} (hd0 : 0<d) (hdU : d<1/2)
    {k : Ambient} (hE : liftedEnergy d k=0) (hg : energyGradient d k=0) :
    ∃ swap : Bool, ∃ n m : ℤ, ∃ e : OpenPartialHomeomorph Ambient Ambient,
      k∈gaugeHomeomorph swap n m '' e.source ∧
      (((e : Ambient → Ambient)=qCoordinates d ∧
          ∀p∈e.source,(fderiv ℝ (sharedFactor d) p) (unit 0)≠0) ∨
       ((e : Ambient → Ambient)=vCoordinates d ∧
          (∀p∈e.source,sharedFactor d p≠0) ∧
          ∀p∈e.source,(fderiv ℝ (PinnedCriticalVAmplitude.coordinateFunction d) p) (unit 2)≠0)) := by
  obtain ⟨swap,n,m,z,v,hk,hcase,hvel⟩ := every_critical_point_normalized hd0 hdU hE hg
  let p : Ambient := WithLp.toLp 2 ![z,0,v]
  have hpk : gaugeHomeomorph swap n m p=k := by rw [gaugeHomeomorph_apply]; exact hk
  by_cases hG : sharedFactor d p=0
  · have hz : deriv (fun t : ℝ=>sharedFactor d (WithLp.toLp 2 ![t,0,v])) z≠0 := by
      rcases hcase with hv | hc
      · subst v
        exact (sharedFactor_origin_alternative hd0 hdU z).resolve_left (not_not.mpr hG)
      · exact (sharedFactor_separated_noncritical hd0 hdU hvel hc).2
    have hn : (fderiv ℝ (sharedFactor d) p) (unit 0)≠0 := by
      rw [PinnedCriticalQCutoff.partial_factorZ hd0 hdU]
      rw [(sharedFactor_z_hasDerivAt hd0 hdU z 0 v).deriv] at hz
      exact hz
    obtain ⟨e,r,δ,he,hr,hδ,hes,_,_,hjac⟩ :=
      ControlledCoordinateChart.exists_chart (sharedFactor_contDiff_one hd0 hdU).contDiffAt 0 hn
    refine ⟨swap,n,m,e,⟨p,?_,hpk⟩,Or.inl ⟨he,?_⟩⟩
    · rw [hes]
      exact Metric.mem_ball_self hr
    · intro q hq
      exact abs_pos.mp (hδ.trans_le (hjac q hq))
  · have hv0 : v=0 := by
      have hvG := sharedFactor_separated hd0 hdU z v
      rw [hvel,sub_self] at hvG
      exact (mul_eq_zero.mp hvG).resolve_right hG
    have hn : (fderiv ℝ (PinnedCriticalVAmplitude.coordinateFunction d) p) (unit 2)≠0 := by
      rw [v_partial_at_zero hd0 hdU (by change v=0; exact hv0)]
      exact hG
    obtain ⟨e,r,δ,he,hr,hδ,hes,_,_,hjac⟩ := ControlledCoordinateChart.exists_chart
      (PinnedCriticalVAmplitude.coordinateFunction_contDiff hd0 hdU).contDiffAt 2 hn
    let S := {q : Ambient|sharedFactor d q≠0}
    have hSo : IsOpen S := (isClosed_eq (sharedFactor_contDiff_one hd0 hdU).continuous continuous_const).isOpen_compl
    let e0 := e.restr S
    have he0 : e0.source=e.source∩S := by rw [e.restr_source' _ hSo]
    refine ⟨swap,n,m,e0,⟨p,?_,hpk⟩,Or.inr ⟨he,?_,?_⟩⟩
    · rw [he0]
      refine ⟨?_,hG⟩
      rw [hes]
      exact Metric.mem_ball_self hr
    · intro q hq
      exact (he0 ▸ hq).2
    · intro q hq
      exact abs_pos.mp (hδ.trans_le (hjac q (he0 ▸ hq).1))

end
end Resonance.PinnedControlledCritical
