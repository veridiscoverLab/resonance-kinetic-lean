import Resonance.FiveInvariantFinal
import Resonance.ActualLinearization

/-! Exact five-moment kernel of the actual normalized RJ linearization on
the original sharp-cube Lebesgue L². Coercivity in the corner-weighted space
is a subsequent estimate and is not assumed here. -/
open Set MeasureTheory Filter
open scoped ENNReal

namespace Resonance.WeightedFiveKernel
noncomputable section
open ResonantMeasure PhysicalMarginal PhysicalCollisionForm
open ContinuousCollisionInvariants QuadraticPointwiseClosure FiveInvariantFinal
open CollisionLocalization WeightedPhysicalForm

theorem polynomial_invariant (R : ℝ) (b : Coefficients) : invariant R (evaluate b) := by
  have hf : ∀ᵐ q ∂pairingMeasure R, q∈fullResonance R :=
    ae_iff.mpr (pairing_supported_on_fullResonance R)
  filter_upwards [hf] with q hq
  have hm := congrArg b.2.1 hq.2.1
  simp only [map_add] at hm
  simp only [evaluate]
  linear_combination hm+b.2.2*hq.2.2

theorem invariant_of_cube_ae_eq {R : ℝ} {f g : E → ℝ}
    (hfg : f =ᵐ[physicalMeasure R] g) (hg : invariant R g) : invariant R f := by
  have hi (i : Fin 4) := (JointMultiplier.leg_quasiMeasurePreserving_cube R i).ae_eq hfg
  filter_upwards [hi 0,hi 1,hi 2,hi 3,hg] with q h0 h1 h2 h3 hq
  simp only [Function.comp_def] at h0 h1 h2 h3
  rw [h0,h1,h2,h3]
  exact hq

theorem divided_L2_locally_integrable {R : ℝ} (hR : 0≤R)
    (θ : Thermodynamics.Parameter) (f : H R) :
    LocallyIntegrableOn (fun x => f x/WeightedJointMeasure.profile θ x) (openCube R) := by
  letI := PhysicalBalance.physicalMeasure_finite hR
  have hi : IntegrableOn (fun x => f x/WeightedJointMeasure.profile θ x) (cube R) :=
    (divide_profile_memLp R θ (Lp.memLp f)).integrable (by norm_num)
  exact hi.locallyIntegrableOn.mono_set (openCube_subset_cube R)

theorem actual_operator_kernel_unique {R : ℝ} (hR : 0<R) {θ : Thermodynamics.Parameter}
    (hθ : θ∈Thermodynamics.positiveDomain R) (f : H R)
    (hf : WeightedOperator.operator hR.le hθ f=0) :
    ∃! b : Coefficients, f =ᵐ[physicalMeasure R]
      (fun x => WeightedJointMeasure.profile θ x*evaluate b x) := by
  obtain ⟨b,hb,hunique⟩ := original_cube_invariant_unique hR
    (divided_L2_locally_integrable hR.le θ f) ((WeightedOperator.operator_eq_zero_iff hR.le hθ f).mp hf)
  have hne : ∀ᵐ x ∂physicalMeasure R, WeightedJointMeasure.profile θ x≠0 := by
    filter_upwards [ae_restrict_mem (measurable_cube R)] with x hx
    exact ne_of_gt (WeightedJointMeasure.profile_pos hθ hx)
  refine ⟨b,?_,?_⟩
  · filter_upwards [hb,hne] with x hx hn
    exact (div_eq_iff hn).mp hx |>.trans (mul_comm _ _)
  · intro c hc
    apply hunique
    filter_upwards [hc,hne] with x hx hn
    rw [hx,mul_div_cancel_left₀ _ hn]

theorem actual_operator_kernel_iff {R : ℝ} (hR : 0<R) {θ : Thermodynamics.Parameter}
    (hθ : θ∈Thermodynamics.positiveDomain R) (f : H R) :
    WeightedOperator.operator hR.le hθ f=0 ↔
      ∃ b : Coefficients, f =ᵐ[physicalMeasure R]
        (fun x => WeightedJointMeasure.profile θ x*evaluate b x) := by
  constructor
  · intro hf
    exact (actual_operator_kernel_unique hR hθ f hf).exists
  · rintro ⟨b,hb⟩
    apply (WeightedOperator.operator_eq_zero_iff hR.le hθ f).mpr
    apply invariant_of_cube_ae_eq (f := fun x => f x/WeightedJointMeasure.profile θ x)
      (g := evaluate b) _ (polynomial_invariant R b)
    filter_upwards [hb,ae_restrict_mem (measurable_cube R)] with x hx hxc
    have hn := ne_of_gt (WeightedJointMeasure.profile_pos hθ hxc)
    rw [hx,mul_div_cancel_left₀ _ hn]

end
end Resonance.WeightedFiveKernel
