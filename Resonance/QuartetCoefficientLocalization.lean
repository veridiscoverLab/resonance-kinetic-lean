import Resonance.AllMarkedQuartetReaders

/-! Signed coefficients on the same quartet. A bulk-small coefficient
may stay bounded at any corner leg; its off-diagonal reader is still small.
No such statement is made for an equal pair of observed legs. -/
open Set MeasureTheory Filter
open scoped ENNReal Topology
namespace Resonance.QuartetCoefficientLocalization
noncomputable section
open ResonantMeasure WeightedJointMeasure FrequencyWeightedForm
open CornerPairTruncation MarkedQuartetOperator AllMarkedQuartetReaders
set_option maxHeartbeats 1800000

def absH (R : ℝ) (θ : Thermodynamics.Parameter) (u : H R θ) : H R θ:=
  (Lp.memLp u).norm.toLp (fun k=>‖u k‖)

theorem absH_ae (R : ℝ) (θ : Thermodynamics.Parameter) (u : H R θ) :
    absH R θ u=ᵐ[marginal R θ] (fun k=>|u k|) := by
  simpa only [Real.norm_eq_abs] using (MemLp.coeFn_toLp (Lp.memLp u).norm)

theorem absH_norm (R : ℝ) (θ : Thermodynamics.Parameter) (u : H R θ) :
    ‖absH R θ u‖=‖u‖ := by
  change ‖(Lp.memLp u).norm.toLp (fun k=>‖u k‖)‖=‖u‖
  rw [Lp.norm_toLp,eLpNorm_norm]
  rfl

theorem actual_product_integrable (R : ℝ) (θ : Thermodynamics.Parameter) (i j : Fin 4)
    (u v : H R θ) : Integrable (fun q=>u (q j)*v (q i)) (jointMeasure R θ) := by
  apply ((Lp.memLp (pullback R θ j u)).integrable_mul (Lp.memLp (pullback R θ i v))).congr
  filter_upwards [pullback_ae R θ j u,pullback_ae R θ i v] with q hu hv
  simp only [Pi.mul_apply,hu,hv]

theorem actual_abs_product_bound (R : ℝ) (θ : Thermodynamics.Parameter) (i j : Fin 4)
    (u v : H R θ) :
    (∫q,|u (q j)| * |v (q i)|∂jointMeasure R θ) ≤ ‖u‖*‖v‖ := by
  have he : (∫q,|u (q j)| * |v (q i)|∂jointMeasure R θ)=
    inner ℝ (pullback R θ i (absH R θ v)) (pullback R θ j (absH R θ u)) := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [pullback_ae R θ i (absH R θ v),pullback_ae R θ j (absH R θ u),
      (all_legs_preserve R θ i).quasiMeasurePreserving.ae_eq (absH_ae R θ v),
      (all_legs_preserve R θ j).quasiMeasurePreserving.ae_eq (absH_ae R θ u)] with q hvi huj hv hu
    change |u (q j)| * |v (q i)|=(pullback R θ j (absH R θ u)) q*(pullback R θ i (absH R θ v)) q
    simp only [Function.comp_def] at hv hu
    rw [hvi,huj,hv,hu]
  rw [he]
  exact (real_inner_le_norm _ _).trans_eq (by rw [(pullback R θ i).norm_map,
    (pullback R θ j).norm_map,absH_norm,absH_norm,mul_comm])

theorem actual_marked_abs_bound {R : ℝ} (hR : 0<R) {θ : Thermodynamics.Parameter}
    (hθ : θ∈Thermodynamics.positiveDomain R) (i j l : Fin 4) (hij : i≠j)
    (η : ℝ) (u v : H R θ) :
    (∫q,cut R η (q l)*|u (q j)| * |v (q i)|∂jointMeasure R θ)
      ≤ markedOmega R θ η*‖u‖*‖v‖ := by
  have he : (∫q,cut R η (q l)*|u (q j)| * |v (q i)|∂jointMeasure R θ)=
    ∫q,cut R η (q l)*(absH R θ u (q j))*(absH R θ v (q i))∂jointMeasure R θ := by
    apply integral_congr_ae
    filter_upwards [(all_legs_preserve R θ i).quasiMeasurePreserving.ae_eq (absH_ae R θ v),
      (all_legs_preserve R θ j).quasiMeasurePreserving.ae_eq (absH_ae R θ u)] with q hv hu
    simp only [Function.comp_def] at hv hu
    rw [hv,hu]
  rw [he]
  have hb:=actual_full_marked_pair_bound hR hθ i j l hij η (absH R θ u) (absH R θ v)
  simpa only [absH_norm] using (le_abs_self _).trans hb

theorem actual_marked_abs_integrable (R : ℝ) (θ : Thermodynamics.Parameter)
    (i j l : Fin 4) (η : ℝ) (u v : H R θ) :
    Integrable (fun q=>cut R η (q l)*|u (q j)| * |v (q i)|) (jointMeasure R θ) := by
  apply (actual_marked_integrable R θ i j l η u v).norm.congr
  apply ae_of_all
  intro q
  simp only [Real.norm_eq_abs,abs_mul,abs_of_nonneg (cut_bounds R η (q l)).1]

/-- A common positive envelope for a real signed full-quartet coefficient. -/
def envelope (R κ M η : ℝ) (q : FourMomenta) : ℝ:=κ+M*(∑l:Fin 4,cut R η (q l))

theorem envelope_nonnegative (R η : ℝ) {κ M : ℝ} (hκ : 0≤κ) (hM : 0≤M)
    (q : FourMomenta) : 0≤envelope R κ M η q :=
  add_nonneg hκ (mul_nonneg hM (Finset.sum_nonneg (fun l _=>(cut_bounds R η (q l)).1)))

theorem actual_envelope_integrable (R : ℝ) (θ : Thermodynamics.Parameter)
    (i j : Fin 4) (κ M η : ℝ) (u v : H R θ) :
    Integrable (fun q=>envelope R κ M η q*|u (q j)| * |v (q i)|) (jointMeasure R θ) := by
  have h0:=((actual_product_integrable R θ i j u v).norm.const_mul κ)
  have h1:=(integrable_finset_sum Finset.univ
    (fun l _=>(actual_marked_abs_integrable R θ i j l η u v).const_mul M))
  apply (h0.add h1).congr
  apply ae_of_all
  intro q
  simp only [Pi.add_apply,Real.norm_eq_abs,abs_mul,envelope,
    Fin.sum_univ_succ,Fin.sum_univ_zero,add_zero]
  ring

theorem actual_envelope_integral_bound {R : ℝ} (hR : 0<R) {θ : Thermodynamics.Parameter}
    (hθ : θ∈Thermodynamics.positiveDomain R) (i j : Fin 4) (hij : i≠j)
    {κ M : ℝ} (hκ : 0≤κ) (hM : 0≤M) (η : ℝ) (u v : H R θ) :
    (∫q,envelope R κ M η q*|u (q j)| * |v (q i)|∂jointMeasure R θ)
      ≤ (κ+4*M*markedOmega R θ η)*‖u‖*‖v‖ := by
  have h0: Integrable (fun q=>|u (q j)| * |v (q i)|) (jointMeasure R θ):=by
    simpa only [Real.norm_eq_abs,abs_mul] using (actual_product_integrable R θ i j u v).norm
  have he : (fun q=>envelope R κ M η q*|u (q j)| * |v (q i)|)=
    (fun q=>κ*(|u (q j)| * |v (q i)|)+∑l:Fin 4,M*(cut R η (q l)*|u (q j)| * |v (q i)|)) := by
    funext q
    simp only [envelope,Fin.sum_univ_succ,Fin.sum_univ_zero,add_zero]
    ring
  rw [he,integral_add (h0.const_mul κ) (integrable_finset_sum _
    (fun l _=>(actual_marked_abs_integrable R θ i j l η u v).const_mul M)),integral_const_mul,
    integral_finset_sum _ (fun l _=>(actual_marked_abs_integrable R θ i j l η u v).const_mul M)]
  simp_rw [integral_const_mul]
  calc
    _ ≤ κ*(‖u‖*‖v‖)+∑_l:Fin 4,M*(markedOmega R θ η*‖u‖*‖v‖) := by
      apply add_le_add (mul_le_mul_of_nonneg_left (actual_abs_product_bound R θ i j u v) hκ)
      exact Finset.sum_le_sum (fun l _=>mul_le_mul_of_nonneg_left
        (actual_marked_abs_bound hR hθ i j l hij η u v) hM)
    _ = _ := by simp; ring

/-- The only coefficient premise is its displayed pointwise amplitude
envelope. The actual measure, all mixed addresses, and all integration and
small-kernel claims have already been proved for the original object. -/
theorem actual_signed_coefficient_bound {R : ℝ} (hR : 0<R) {θ : Thermodynamics.Parameter}
    (hθ : θ∈Thermodynamics.positiveDomain R) (i j : Fin 4) (hij : i≠j)
    {κ M : ℝ} (hκ : 0≤κ) (hM : 0≤M) (η : ℝ) (u v : H R θ)
    {a : FourMomenta→ℝ} (ha : AEStronglyMeasurable a (jointMeasure R θ))
    (hb : ∀ᵐq∂jointMeasure R θ, |a q|≤envelope R κ M η q) :
    Integrable (fun q=>a q*u (q j)*v (q i)) (jointMeasure R θ) ∧
    |∫q,a q*u (q j)*v (q i)∂jointMeasure R θ|
      ≤ (κ+4*M*markedOmega R θ η)*‖u‖*‖v‖ := by
  have hi:=actual_envelope_integrable R θ i j κ M η u v
  have hd : ∀ᵐq∂jointMeasure R θ, ‖a q*u (q j)*v (q i)‖≤
      envelope R κ M η q*|u (q j)| * |v (q i)| := by
    filter_upwards [hb] with q hq
    simp only [Real.norm_eq_abs,abs_mul]
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hq (abs_nonneg _)) (abs_nonneg _)
  have hm := ha.mul (((Lp.stronglyMeasurable u).measurable.comp
    (measurable_pi_apply j)).aestronglyMeasurable)
  have hm' := hm.mul (((Lp.stronglyMeasurable v).measurable.comp
    (measurable_pi_apply i)).aestronglyMeasurable)
  have haf := hi.mono' hm' hd
  refine ⟨haf,?_⟩
  exact (norm_integral_le_of_norm_le hi hd).trans
    (actual_envelope_integral_bound hR hθ i j hij hκ hM η u v)

end
end Resonance.QuartetCoefficientLocalization
