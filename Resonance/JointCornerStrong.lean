import Resonance.MarkedQuartetOperator
import Resonance.QuartetCoefficientLocalization

/-! Strong convergence on the original whole-quartet space, including
all equal observed-leg readers. No small operator norm for a diagonal
corner reader is asserted. -/
open Set MeasureTheory Filter
open scoped ENNReal Topology
namespace Resonance.JointCornerStrong
noncomputable section
open ResonantMeasure WeightedJointMeasure FrequencyWeightedForm
open CornerPairTruncation MarkedQuartetOperator LpOperators QuartetCoefficientLocalization
set_option maxHeartbeats 2200000

theorem jointCut_ae (R : ℝ) (θ : Thermodynamics.Parameter) (l : Fin 4)
    (η : ℝ) (u : J R θ) :
    jointCut R θ l η u =ᵐ[jointMeasure R θ] (fun q=>u q*cut R η (q l)) :=
  multiply_ae (jointCut_memLp R θ l η) u

theorem jointCut_norm_square (R : ℝ) (θ : Thermodynamics.Parameter) (l : Fin 4)
    (η : ℝ) (u : J R θ) :
    ‖jointCut R θ l η u‖^2=∫q,(u q*cut R η (q l))^2∂jointMeasure R θ := by
  rw [←real_inner_self_eq_norm_sq,L2.inner_def]
  apply integral_congr_ae
  filter_upwards [jointCut_ae R θ l η u] with q hq
  change jointCut R θ l η u q*jointCut R θ l η u q = _
  rw [hq,pow_two]

theorem actual_jointCut_strong {R : ℝ} (hR : 0 < R) (θ : Thermodynamics.Parameter)
    (l : Fin 4) (u : J R θ) :
    Tendsto (fun η:ℝ=>jointCut R θ l η u) (𝓝 0) (𝓝 0) := by
  have ht : Tendsto (fun η:ℝ=>∫q,(u q*cut R η (q l))^2∂jointMeasure R θ)
      (𝓝 0) (𝓝 0) := by
    have hh:=tendsto_integral_filter_of_dominated_convergence
      (μ:=jointMeasure R θ) (l:=𝓝 (0:ℝ))
      (F:=fun η q=>(u q*cut R η (q l))^2) (f:=fun _=>0) (fun q=>(u q)^2)
    simp only [integral_zero] at hh
    apply hh
    · exact Eventually.of_forall (fun η=>((Lp.memLp u).aestronglyMeasurable.mul
        (jointCut_memLp R θ l η).aestronglyMeasurable).pow 2)
    · apply Eventually.of_forall
      intro η
      apply ae_of_all
      intro q
      rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
      have hb : |u q*cut R η (q l)| ≤ |u q| := by
        rw [abs_mul]
        exact (mul_le_mul_of_nonneg_left (cut_bounds R η (q l)).2 (abs_nonneg _)).trans_eq (mul_one _)
      simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) hb 2
    · exact (Lp.memLp u).integrable_sq
    · filter_upwards [(all_legs_preserve R θ l).quasiMeasurePreserving.ae
        (depth_positive_marginal hR θ)] with q hq
      simpa only [mul_zero,zero_pow (by norm_num:2≠0)] using
        ((tendsto_const_nhds (x:=u q)).mul (cut_tendsto hq)).pow 2
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  have he : (fun η:ℝ=>‖jointCut R θ l η u‖)=
      (fun η=>Real.sqrt (∫q,(u q*cut R η (q l))^2∂jointMeasure R θ)) := by
    funext η
    rw [←jointCut_norm_square,Real.sqrt_sq_eq_abs,abs_of_nonneg (norm_nonneg _)]
  rw [he]
  simpa only [Real.sqrt_zero] using (Real.continuous_sqrt.tendsto 0).comp ht

/-- The two observed legs may be equal; the marker stays on the same
original quartet and may be any of its four legs. -/
theorem actual_all_readers_strong {R : ℝ} (hR : 0 < R) (θ : Thermodynamics.Parameter)
    (i j l : Fin 4) (u : H R θ) :
    Tendsto (fun η:ℝ=>markedOperator R θ i j l η u) (𝓝 0) (𝓝 0) := by
  have hh:=((pullback R θ i).toContinuousLinearMap.adjoint.continuous.tendsto 0).comp
    (actual_jointCut_strong hR θ l (pullback R θ j u))
  simpa only [map_zero] using hh

theorem finset_sum_ae {A : Type*} (s : Finset A) (R : ℝ) (θ : Thermodynamics.Parameter)
    (u : A→J R θ) :
    ((∑a∈s,u a):J R θ) =ᵐ[jointMeasure R θ] (fun q=>∑a∈s,u a q) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa only [Finset.sum_empty] using (Lp.coeFn_zero (E:=ℝ) (p:=2) (μ:=jointMeasure R θ))
  | @insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    filter_upwards [Lp.coeFn_add (u a) (∑b∈s,u b),ih] with q hq hi
    simp only [Pi.add_apply] at hq
    rw [hq,hi]

/-- Actual joint multiplication with a displayed full four-mark envelope. -/
theorem joint_envelope_norm (R : ℝ) (θ : Thermodynamics.Parameter) (η : ℝ)
    {b : FourMomenta→ℝ} (hb : MemLp b ∞ (jointMeasure R θ))
    {κ M : ℝ} (hκ : 0 ≤ κ) (hM : 0 ≤ M)
    (henv : ∀ᵐq∂jointMeasure R θ, |b q| ≤ envelope R κ M η q) (u : J R θ) :
    ‖multiplyCLM hb u‖ ≤ κ*‖u‖+M*(∑l:Fin 4,‖jointCut R θ l η u‖) := by
  let w : J R θ:=κ • u+M • (∑l:Fin 4,jointCut R θ l η u)
  have hn : ‖multiplyCLM hb u‖ ≤ ‖w‖ := by
    apply Lp.norm_le_norm_of_ae_le
    have hall : ∀ᵐq∂jointMeasure R θ,∀l:Fin 4,
        jointCut R θ l η u q=u q*cut R η (q l) :=
      ae_all_iff.mpr (fun l=>jointCut_ae R θ l η u)
    filter_upwards [multiply_ae hb u,henv,hall,
      finset_sum_ae Finset.univ R θ (fun l:Fin 4=>jointCut R θ l η u),
      Lp.coeFn_add (κ • u) (M • (∑l:Fin 4,jointCut R θ l η u)),
      Lp.coeFn_smul κ u,Lp.coeFn_smul M (∑l:Fin 4,jointCut R θ l η u)] with q hbq he hcuts hsum ha hsu hsc
    change multiplyCLM hb u q=u q*b q at hbq
    simp only [Pi.add_apply] at ha
    simp only [Pi.smul_apply,smul_eq_mul] at hsu hsc
    change |multiplyCLM hb u q| ≤ |(κ • u+M • (∑l:Fin 4,jointCut R θ l η u)) q|
    rw [hbq,ha,hsu,hsc,hsum]
    simp_rw [hcuts]
    have hw : κ*u q+M*(∑l:Fin 4,u q*cut R η (q l))=u q*envelope R κ M η q := by
      simp only [envelope,←Finset.mul_sum]
      ring
    rw [hw,abs_mul,abs_mul,abs_of_nonneg (envelope_nonnegative R η hκ hM q)]
    exact mul_le_mul_of_nonneg_left he (abs_nonneg _)
  refine hn.trans ((norm_add_le _ _).trans ?_)
  rw [norm_smul,norm_smul,Real.norm_eq_abs,Real.norm_eq_abs,
    abs_of_nonneg hκ,abs_of_nonneg hM]
  exact add_le_add le_rfl (mul_le_mul_of_nonneg_left (norm_sum_le _ _) hM)

theorem actual_joint_envelope_strong {I : Type*} {R : ℝ} (hR : 0 < R)
    (θ : Thermodynamics.Parameter) (l : Filter I) (b : I→FourMomenta→ℝ)
    (hb : ∀i,MemLp (b i) ∞ (jointMeasure R θ)) (κ η : I→ℝ) {M : ℝ}
    (hM : 0 ≤ M) (henv : ∀i,∀ᵐq∂jointMeasure R θ, |b i q| ≤ envelope R |κ i| M (η i) q)
    (hκ : Tendsto κ l (𝓝 0)) (hη : Tendsto η l (𝓝 0)) (u : J R θ) :
    Tendsto (fun i=>multiplyCLM (hb i) u) l (𝓝 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  have hsum := tendsto_finset_sum (Finset.univ:Finset (Fin 4)) (fun j _=>
    (((actual_jointCut_strong hR θ j u).comp hη).norm))
  simp only [norm_zero,Finset.sum_const_zero] at hsum
  have ht:=((hκ.abs).mul_const ‖u‖).add (hsum.const_mul M)
  simp only [abs_zero,zero_mul,mul_zero,add_zero] at ht
  exact squeeze_zero (fun _=>norm_nonneg _)
    (fun i=>joint_envelope_norm R θ (η i) (hb i) (abs_nonneg _) hM (henv i) u) ht

end
end Resonance.JointCornerStrong
