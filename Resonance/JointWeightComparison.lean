import Resonance.ActualWeightedCoercivity
import Resonance.LpOperators

/-! Uniform comparison of the same complete quartet and its marginals,
derived from the actual RJ parameter domain on the closed cube. -/
open MeasureTheory Set
open scoped ENNReal
namespace Resonance.JointWeightComparison
noncomputable section
open ResonantMeasure WeightedJointMeasure Thermodynamics FrequencyWeightedForm

def unitParameter : Parameter := ![1,0,0,0,0]

theorem unitParameter_positive (R : ℝ) : unitParameter∈positiveDomain R := by
  intro k _hk
  norm_num [unitParameter,Entropy.denominator,Entropy.fiveInvariants,Fin.sum_univ_succ]

theorem unit_profile (k : E) : profile unitParameter k=1 := by
  simp [profile,unitParameter,Entropy.rj,Entropy.denominator,Entropy.fiveInvariants,
    Fin.sum_univ_succ]

theorem unit_joint (R : ℝ) : jointMeasure R unitParameter=pairingMeasure R := by
  have hw : weight unitParameter=(fun _=>1) := by
    funext q
    simp only [weight,unit_profile,Finset.prod_const_one,ENNReal.ofReal_one]
  rw [jointMeasure,hw]
  exact withDensity_one

theorem joint_weight_le {R M : ℝ} {θ : Parameter}
    (hθ : θ∈positiveDomain R) (hb : ∀k∈cube R,profile θ k≤M) :
    jointMeasure R θ≤ENNReal.ofReal (M^4) • pairingMeasure R := by
  have hw : weight θ≤ᵐ[pairingMeasure R] (fun _=>ENNReal.ofReal (M^4)) := by
    filter_upwards [ae_iff.mpr (pairing_supported_on_fullResonance R)] with q hq
    apply ENNReal.ofReal_le_ofReal
    calc
      _ ≤ ∏_i : Fin 4,M := Finset.prod_le_prod (fun i _=>(profile_pos hθ (hq.1 i)).le)
        (fun i _=>hb _ (hq.1 i))
      _ = M^4 := by simp
  simpa only [jointMeasure,withDensity_const] using withDensity_mono hw

theorem joint_weight_ge {R m : ℝ} (hm : 0 < m) {θ : Parameter}
    (hb : ∀k∈cube R,m≤profile θ k) :
    ENNReal.ofReal (m^4) • pairingMeasure R≤jointMeasure R θ := by
  have hw : (fun _=>ENNReal.ofReal (m^4))≤ᵐ[pairingMeasure R] weight θ := by
    filter_upwards [ae_iff.mpr (pairing_supported_on_fullResonance R)] with q hq
    apply ENNReal.ofReal_le_ofReal
    calc
      _ = ∏_i : Fin 4,m := by simp
      _ ≤ _ := Finset.prod_le_prod (fun _ _=>hm.le) (fun i _=>hb _ (hq.1 i))
  simpa only [jointMeasure,withDensity_const] using withDensity_mono hw

theorem joint_weight_reverse {R m : ℝ} (hm : 0 < m) {θ : Parameter}
    (hb : ∀k∈cube R,m≤profile θ k) :
    pairingMeasure R≤(ENNReal.ofReal (m^4))⁻¹ • jointMeasure R θ := by
  have h := joint_weight_ge hm hb
  have hh : (ENNReal.ofReal (m^4))⁻¹ • (ENNReal.ofReal (m^4) • pairingMeasure R)≤
      (ENNReal.ofReal (m^4))⁻¹ • jointMeasure R θ := by
    intro s
    exact mul_le_mul' le_rfl (h s)
  simpa only [smul_smul,ENNReal.inv_mul_cancel (ENNReal.ofReal_pos.mpr (pow_pos hm 4)).ne'
    ENNReal.ofReal_ne_top,one_smul] using hh

theorem marginal_of_joint_comparison {R : ℝ} {θ β : Parameter} {C : ℝ≥0∞}
    (h : jointMeasure R θ≤C • jointMeasure R β) :
    marginal R θ≤C • marginal R β := by
  have hh := Measure.map_mono h (measurable_pi_apply (0 : Fin 4))
  simpa only [marginal,Measure.map_smul] using hh

theorem compact_profile_bounds {R : ℝ} (hR : 0≤R) {K : Set Parameter}
    (hK : IsCompact K) (hpos : K⊆positiveDomain R) :
    ∃m M : ℝ,0 < m ∧ 0 < M ∧ ∀θ∈K,∀k∈cube R,m≤profile θ k ∧ profile θ k≤M := by
  by_cases hne : K.Nonempty
  · have hcube : (cube R).Nonempty := ⟨0,by simpa [cube] using hR⟩
    have hc : ContinuousOn (fun p : Parameter×E=>profile p.1 p.2) (K×ˢcube R) := by
      have hd : Continuous (fun p : Parameter×E=>
          Entropy.denominator Entropy.fiveInvariants p.1 (coordinates p.2)) :=
        denominator_joint_continuous.comp
          (continuous_fst.prodMk (coordinates_continuous.comp continuous_snd))
      apply hd.continuousOn.inv₀
      intro p hp
      exact ne_of_gt (hpos hp.1 _ ((coordinates_cube R p.2).mp hp.2))
    obtain ⟨p,hp,hmin⟩ := (hK.prod (FiberContinuity.cube_isCompact R)).exists_isMinOn
      (hne.prod hcube) hc
    obtain ⟨q,hq,hmax⟩ := (hK.prod (FiberContinuity.cube_isCompact R)).exists_isMaxOn
      (hne.prod hcube) hc
    refine ⟨profile p.1 p.2,profile q.1 q.2,profile_pos (hpos hp.1) hp.2,
      profile_pos (hpos hq.1) hq.2,?_⟩
    intro θ hθ k hk
    exact ⟨hmin (show (θ,k)∈K×ˢcube R from ⟨hθ,hk⟩),
      hmax (show (θ,k)∈K×ˢcube R from ⟨hθ,hk⟩)⟩
  · refine ⟨1,1,by norm_num,by norm_num,?_⟩
    intro θ hθ
    exact (hne ⟨θ,hθ⟩).elim

end
end Resonance.JointWeightComparison
