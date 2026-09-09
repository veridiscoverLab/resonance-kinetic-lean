import Resonance.CollisionMarginalDensity
import Resonance.WeightedFiveKernel

/-! The full difference in the actual marginal-weighted space.  The marginal
is exactly N² nu_N dk; its variable is the reciprocal perturbation u/N.
All four legs are isometries into one common weighted quartet space. -/
open MeasureTheory Set Filter
open scoped ENNReal Topology
namespace Resonance.FrequencyWeightedForm
noncomputable section
open ResonantMeasure WeightedJointMeasure CollisionMarginalDensity

def marginal (R : ℝ) (θ : Thermodynamics.Parameter) : Measure E :=
  (jointMeasure R θ).map (fun q=>q 0)

theorem all_legs_preserve (R : ℝ) (θ : Thermodynamics.Parameter) (i : Fin 4) :
    MeasurePreserving (fun q : FourMomenta=>q i) (jointMeasure R θ) (marginal R θ) :=
  ⟨measurable_pi_apply i,marginal_eq_first R θ i⟩

theorem marginal_frequency {R : ℝ} (hR : 0≤R) {θ : Thermodynamics.Parameter}
    (hθ : θ∈Thermodynamics.positiveDomain R) :
    marginal R θ=(frequencyMeasure R θ).withDensity (fun k=>ENNReal.ofReal ((profile θ k)^2)) :=
  weighted_all_marginals_frequency hR hθ 0

abbrev H (R : ℝ) (θ : Thermodynamics.Parameter) := Lp ℝ 2 (marginal R θ)
abbrev J (R : ℝ) (θ : Thermodynamics.Parameter) := Lp ℝ 2 (jointMeasure R θ)

def pullback (R : ℝ) (θ : Thermodynamics.Parameter) (i : Fin 4) : H R θ→ₗᵢ[ℝ]J R θ :=
  Lp.compMeasurePreservingₗᵢ ℝ (fun q : FourMomenta=>q i) (all_legs_preserve R θ i)

theorem pullback_ae (R : ℝ) (θ : Thermodynamics.Parameter) (i : Fin 4) (f : H R θ) :
    pullback R θ i f=ᵐ[jointMeasure R θ] (fun q=>f (q i)) :=
  Lp.coeFn_compMeasurePreserving f (all_legs_preserve R θ i)

def fullDifference (R : ℝ) (θ : Thermodynamics.Parameter) : H R θ→L[ℝ]J R θ :=
  (1/2 : ℝ) • ((pullback R θ 0).toContinuousLinearMap +
    (pullback R θ 1).toContinuousLinearMap - (pullback R θ 2).toContinuousLinearMap -
    (pullback R θ 3).toContinuousLinearMap)

theorem fullDifference_ae (R : ℝ) (θ : Thermodynamics.Parameter) (f : H R θ) :
    fullDifference R θ f=ᵐ[jointMeasure R θ] CollisionForm.rawDifference f := by
  let a := pullback R θ 0 f
  let b := pullback R θ 1 f
  let c := pullback R θ 2 f
  let d := pullback R θ 3 f
  change ((1/2 : ℝ) • (a+b-c-d) : J R θ)=ᵐ[jointMeasure R θ] _
  filter_upwards [pullback_ae R θ 0 f,pullback_ae R θ 1 f,pullback_ae R θ 2 f,
    pullback_ae R θ 3 f,Lp.coeFn_add a b,Lp.coeFn_sub (a+b) c,
    Lp.coeFn_sub (a+b-c) d,Lp.coeFn_smul (1/2 : ℝ) (a+b-c-d)]
    with q h0 h1 h2 h3 ha hb hc hd
  simp only [Pi.sub_apply,Pi.add_apply,Pi.smul_apply] at ha hb hc hd
  rw [hd,hc,hb,ha]
  change (1/2 : ℝ)*((pullback R θ 0 f) q+(pullback R θ 1 f) q-
    (pullback R θ 2 f) q-(pullback R θ 3 f) q)=CollisionForm.rawDifference f q
  rw [h0,h1,h2,h3]
  rfl

theorem fullDifference_bound (R : ℝ) (θ : Thermodynamics.Parameter) (f : H R θ) :
    ‖fullDifference R θ f‖≤2*‖f‖ := by
  change ‖(1/2 : ℝ) • (pullback R θ 0 f+pullback R θ 1 f-
    pullback R θ 2 f-pullback R θ 3 f)‖≤_
  rw [norm_smul,Real.norm_eq_abs,abs_of_pos (by norm_num : (0:ℝ)<1/2)]
  have h0 := norm_add_le (pullback R θ 0 f) (pullback R θ 1 f)
  have h1 := norm_sub_le (pullback R θ 0 f+pullback R θ 1 f) (pullback R θ 2 f)
  have h2 := norm_sub_le (pullback R θ 0 f+pullback R θ 1 f-pullback R θ 2 f)
    (pullback R θ 3 f)
  simp only [LinearIsometry.norm_map] at h0 h1 h2
  linarith

def gram (R : ℝ) (θ : Thermodynamics.Parameter) : H R θ→L[ℝ]H R θ :=
  (fullDifference R θ).adjoint.comp (fullDifference R θ)

theorem gram_pairing (R : ℝ) (θ : Thermodynamics.Parameter) (f g : H R θ) :
    inner ℝ f (gram R θ g)=inner ℝ (fullDifference R θ f) (fullDifference R θ g) :=
  ContinuousLinearMap.adjoint_inner_right (fullDifference R θ) f (fullDifference R θ g)

theorem gram_nonnegative (R : ℝ) (θ : Thermodynamics.Parameter) (f : H R θ) :
    0 ≤ inner ℝ f (gram R θ f) := by
  rw [gram_pairing,real_inner_self_eq_norm_sq]
  positivity

theorem gram_selfAdjoint (R : ℝ) (θ : Thermodynamics.Parameter) :
    IsSelfAdjoint (gram R θ) := by
  apply ContinuousLinearMap.isSelfAdjoint_iff'.mpr
  simp [gram,ContinuousLinearMap.adjoint_comp]

theorem gram_kernel (R : ℝ) (θ : Thermodynamics.Parameter) :
    (gram R θ).ker=(fullDifference R θ).ker :=
  ContinuousLinearMap.ker_adjoint_comp_self (fullDifference R θ)

theorem full_form_integrable (R : ℝ) (θ : Thermodynamics.Parameter) (f g : H R θ) :
    Integrable (fun q=>CollisionForm.rawDifference f q*CollisionForm.rawDifference g q)
      (jointMeasure R θ) := by
  apply (L2.integrable_inner (fullDifference R θ f) (fullDifference R θ g)).congr
  filter_upwards [fullDifference_ae R θ f,fullDifference_ae R θ g] with q hf hg
  rw [hf,hg]
  exact mul_comm _ _

theorem gram_integral (R : ℝ) (θ : Thermodynamics.Parameter) (f g : H R θ) :
    inner ℝ f (gram R θ g)=
      ∫q,CollisionForm.rawDifference f q*CollisionForm.rawDifference g q∂jointMeasure R θ := by
  rw [gram_pairing,L2.inner_def]
  apply integral_congr_ae
  filter_upwards [fullDifference_ae R θ f,fullDifference_ae R θ g] with q hf hg
  rw [hf,hg]
  exact mul_comm _ _

theorem gram_zero_iff (R : ℝ) {θ : Thermodynamics.Parameter}
    (hθ : θ∈Thermodynamics.positiveDomain R) (f : H R θ) :
    gram R θ f=0 ↔ ContinuousCollisionInvariants.invariant R f := by
  have hk : gram R θ f=0 ↔ fullDifference R θ f=0 := by
    change f∈(gram R θ).ker ↔ f∈(fullDifference R θ).ker
    rw [gram_kernel]
  rw [hk]
  constructor
  · intro hz
    have h := fullDifference_ae R θ f
    rw [hz] at h
    apply (pairing_absolutelyContinuous hθ).ae_le
    filter_upwards [h,Lp.coeFn_zero ℝ 2 (jointMeasure R θ)] with q hq h0
    have he : CollisionForm.rawDifference f q=0 := hq.symm.trans h0
    dsimp [CollisionForm.rawDifference] at he
    linarith
  · intro h
    apply Lp.ext
    filter_upwards [fullDifference_ae R θ f,(joint_absolutelyContinuous R θ).ae_le h,
      Lp.coeFn_zero ℝ 2 (jointMeasure R θ)] with q hq he h0
    rw [hq,h0]
    dsimp [CollisionForm.rawDifference]
    linarith

end
end Resonance.FrequencyWeightedForm
