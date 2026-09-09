import Resonance.ShiftedKernelBounds

/-! Vanishing shift for the actual signed collision correction in
operator norm, proved through the same full incoming and crossed rows. -/
open MeasureTheory Set Filter
open scoped ENNReal Topology
namespace Resonance.ShiftedOperatorLimit
noncomputable section
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
open ResonantMeasure Thermodynamics WeightedJointMeasure CollisionFrequency
open ActualPairNormalization ActualReferenceRowOperator JointWeightComparison
open LinftyParameterContinuity NormalizedPairParameterBounds ShiftRowVanishing

theorem base_cutoff_integrable {R : ℝ} (hR : 0<R) {θ : Parameter}
    (hθ : θ∈positiveDomain R) (n : ℕ) (k : cube R) :
    Integrable (fun p=>baseRow R k p*cutoff R θ n p) (cubeVolume R) := by
  obtain ⟨M,hM,hb⟩ := baseRow_uniform_bound hR
  apply (hb k k.property).1.mul_bdd (cutoff_measurable R θ n).aestronglyMeasurable
  filter_upwards [ae_restrict_mem (measurable_cube R)] with p hp
  rw [Real.norm_of_nonneg (cutoff_bounds hR hθ n hp).1]
  exact (cutoff_bounds hR hθ n hp).2

theorem base_cutoff_eq {R : ℝ} (hR : 0<R) {θ : Parameter}
    (hθ : θ∈positiveDomain R) (n : ℕ) (k : cube R) :
    (∫p,baseRow R k p*cutoff R θ n p∂cubeVolume R)=
      (∫p,incomingRow R unitParameter k p*cutoff R θ n p∂cubeMeasure R)+
        2*(∫p,crossRow R unitParameter k p*cutoff R θ n p∂cubeMeasure R) := by
  have hm : AEStronglyMeasurable (fun p : cube R=>cutoff R θ n p) (cubeMeasure R) :=
    ((cutoff_measurable R θ n).comp measurable_subtype_coe).aestronglyMeasurable
  have hb : ∀ᵐ(p : cube R)∂cubeMeasure R,‖cutoff R θ n (p:E)‖≤1 := by
    filter_upwards [] with p
    rw [Real.norm_of_nonneg (cutoff_bounds hR hθ n p.property).1]
    exact (cutoff_bounds hR hθ n p.property).2
  have hi := (incomingRow_integrable hR (unitParameter_positive R) k).mul_bdd hm hb
  have hc := (crossRow_integrable hR (unitParameter_positive R) k).mul_bdd hm hb
  change (∫p in cube R,baseRow R k p*cutoff R θ n p)=_
  rw [←integral_subtype_comap (measurable_cube R) (fun p=>baseRow R k p*cutoff R θ n p)]
  change (∫p,baseRow R k p*cutoff R θ n p∂cubeMeasure R)=_
  have he (p : cube R) : baseRow R k p*cutoff R θ n p=
      incomingRow R unitParameter k p*cutoff R θ n p+
        2*(crossRow R unitParameter k p*cutoff R θ n p) := by
    unfold baseRow baseDensity incomingRow crossRow
    ring
  simp_rw [he]
  rw [integral_add hi (hc.const_mul 2),integral_const_mul]

theorem base_cutoff_uniform_small {R : ℝ} (hR : 0<R) {θ : Parameter}
    (hθ : θ∈positiveDomain R) {ε : ℝ} (hε : 0<ε) :
    ∀ᶠn in atTop,∀k : cube R,(∫p,baseRow R k p*cutoff R θ n p∂cubeVolume R)<ε := by
  have hi := Metric.tendstoUniformly_iff.mp (incoming_cutoff_vanishes hR hθ) (ε/4) (by positivity)
  have hc := Metric.tendstoUniformly_iff.mp (cross_cutoff_vanishes hR hθ) (ε/4) (by positivity)
  filter_upwards [hi,hc] with n hn hc
  intro k
  rw [base_cutoff_eq hR hθ n k]
  have h1 := hn k
  have h2 := hc k
  rw [dist_zero_left,Real.norm_eq_abs] at h1 h2
  have a1 := (le_abs_self _).trans_lt h1
  have a2 := (le_abs_self _).trans_lt h2
  linarith

theorem shifted_output_bound {R : ℝ} (hR : 0<R) {θ : Parameter}
    (hθ : θ∈positiveDomain R) {C ε : ℝ} (hC : 0≤C) (hε : 0≤ε)
    (hb : ∀k∈cube R,∀p∈cube R,0<geometricFrequency R p →
      ‖AmbientLinftyCompact.kernel R θ k p‖≤C*baseRow R k p)
    (n : ℕ) {z : ℝ} (hz : 0≤z) (hzn : z ≤ scale n)
    (hr : ∀k : cube R,(∫p,baseRow R k p*cutoff R θ n p∂cubeVolume R)≤ε) :
    ‖(AmbientLinftyCompact.continuousOutput hR hθ).comp
      (PositiveLossShift.multiplier hR hθ hz)-
        AmbientLinftyCompact.continuousOutput hR hθ‖≤C*ε := by
  apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg hC hε)
  intro F
  apply (ContinuousMap.norm_le _ (by positivity)).mpr
  intro k
  let M := PositiveLossShift.multiplier hR hθ hz
  change ‖AmbientLinftyCompact.continuousOutput hR hθ (M F) k-
    AmbientLinftyCompact.continuousOutput hR hθ F k‖≤_
  obtain ⟨hi,hei⟩ := AmbientLinftyCompact.continuousOutput_integrable_apply hR hθ (M F) k
  obtain ⟨ho,heo⟩ := AmbientLinftyCompact.continuousOutput_integrable_apply hR hθ F k
  rw [hei,heo,←integral_sub hi ho]
  have hbd : ‖∫p,AmbientLinftyCompact.kernel R θ k p*(M F) p-
      AmbientLinftyCompact.kernel R θ k p*F p∂cubeVolume R‖≤
      ∫p,(C*‖F‖)*(baseRow R k p*cutoff R θ n p)∂cubeVolume R := by
    apply norm_integral_le_of_norm_le ((base_cutoff_integrable hR hθ n k).const_mul _)
    filter_upwards [PositiveLossShift.multiplier_ae hR hθ hz F,
      LinftyRowOperator.ae_norm_bound F,ae_restrict_mem (measurable_cube R),
      LinftyPhysicalDomain.loss_positive_ae hR hθ,geometricFrequency_positive_ae hR]
        with p hm hf hp hn hg
    change (M F) p=F p*PositiveLossShift.fraction R θ z p at hm
    rw [hm]
    have he : AmbientLinftyCompact.kernel R θ k p*(F p*PositiveLossShift.fraction R θ z p)-
        AmbientLinftyCompact.kernel R θ k p*F p=
        -(AmbientLinftyCompact.kernel R θ k p*F p)*(z/(lossFrequency R (profile θ) p+z)) := by
      have hden := (add_pos_of_pos_of_nonneg hn hz).ne'
      unfold PositiveLossShift.fraction
      field_simp
      ring
    have hgap : z/(lossFrequency R (profile θ) p+z)≤cutoff R θ n p := by
      unfold cutoff
      apply (div_le_div_iff₀ (add_pos_of_pos_of_nonneg hn hz) (add_pos hn (scale_pos n))).mpr
      nlinarith
    have hgap0 : 0≤z/(lossFrequency R (profile θ) p+z) := div_nonneg hz (add_nonneg hn.le hz)
    rw [he,norm_mul,norm_neg,norm_mul,Real.norm_of_nonneg hgap0]
    exact (mul_le_mul
      (mul_le_mul (hb k k.property p hp hg) hf (norm_nonneg _) (mul_nonneg hC (baseRow_nonnegative R k p)))
      hgap hgap0 (mul_nonneg (mul_nonneg hC (baseRow_nonnegative R k p)) (norm_nonneg F))).trans_eq (by ring)
  apply hbd.trans
  rw [integral_const_mul]
  exact (mul_le_mul_of_nonneg_left (hr k) (mul_nonneg hC (norm_nonneg _))).trans_eq (by ring)

theorem actual_shifted_output_tendsto {R : ℝ} (hR : 0<R) {θ : Parameter}
    (hθ : θ∈positiveDomain R) :
    Tendsto (fun n=>‖(AmbientLinftyCompact.continuousOutput hR hθ).comp
      (PositiveLossShift.multiplier hR hθ (scale_pos n).le)-
        AmbientLinftyCompact.continuousOutput hR hθ‖) atTop (𝓝 0) := by
  obtain ⟨C,hC,hb⟩ := ShiftedKernelBounds.actual_kernel_reference_bound hR hθ
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have hh := base_cutoff_uniform_small hR hθ (ε:=ε/(2*(C+1))) (by positivity)
  filter_upwards [hh] with n hn
  rw [Real.dist_eq,sub_zero,abs_of_nonneg]
  swap
  · positivity
  apply (shifted_output_bound hR hθ hC (by positivity) hb n (scale_pos n).le le_rfl
    (fun k=>(hn k).le)).trans_lt
  have hp : 0<2*(C+1) := by positivity
  rw [←mul_div_assoc]
  apply (div_lt_iff₀ hp).mpr
  nlinarith

theorem actual_shifted_output_continuousAt_zero {R : ℝ} (hR : 0<R) {θ : Parameter}
    (hθ : θ∈positiveDomain R) :
    Tendsto (fun z : Set.Ici (0:ℝ)=>(AmbientLinftyCompact.continuousOutput hR hθ).comp
      (PositiveLossShift.multiplier hR hθ z.property)) (𝓝 ⟨0,show (0:ℝ)≤0 from le_rfl⟩)
        (𝓝 (AmbientLinftyCompact.continuousOutput hR hθ)) := by
  obtain ⟨C,hC,hb⟩ := ShiftedKernelBounds.actual_kernel_reference_bound hR hθ
  apply (tendsto_iff_norm_sub_tendsto_zero
    (E := Lp ℝ ∞ (cubeVolume R) →L[ℝ] C(cube R,ℝ))).mpr
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨n,hn⟩ := (base_cutoff_uniform_small hR hθ (ε:=ε/(2*(C+1))) (by positivity)).exists
  have he : ∀ᶠz : Set.Ici (0:ℝ) in 𝓝 ⟨0,show (0:ℝ)≤0 from le_rfl⟩,(z:ℝ)<scale n :=
    (continuous_subtype_val.tendsto (⟨0,show (0:ℝ)≤0 from le_rfl⟩ : Set.Ici (0:ℝ))).eventually
      (gt_mem_nhds (scale_pos n))
  filter_upwards [he] with z hz
  rw [Real.dist_eq,sub_zero,abs_of_nonneg]
  swap
  · positivity
  apply (shifted_output_bound hR hθ hC (by positivity) hb n z.property hz.le
    (fun k=>(hn k).le)).trans_lt
  have hp : 0<2*(C+1) := by positivity
  rw [←mul_div_assoc]
  apply (div_lt_iff₀ hp).mpr
  nlinarith

theorem actual_shifted_operator_continuousAt_zero {R : ℝ} (hR : 0<R) {θ : Parameter}
    (hθ : θ∈positiveDomain R) :
    Tendsto (fun z : Set.Ici (0:ℝ)=>(AmbientLinftyCompact.operator hR hθ).comp
      (PositiveLossShift.multiplier hR hθ z.property)) (𝓝 ⟨0,show (0:ℝ)≤0 from le_rfl⟩)
        (𝓝 (AmbientLinftyCompact.operator hR hθ)) := by
  have hc : Continuous (fun T : Lp ℝ ∞ (cubeVolume R)→L[ℝ]C(cube R,ℝ)=>
      (CubeLinftyCoordinates.embed R).comp T) := continuous_const.clm_comp continuous_id
  have hh := hc.continuousAt.tendsto.comp (actual_shifted_output_continuousAt_zero hR hθ)
  simpa only [AmbientLinftyCompact.operator,ContinuousLinearMap.comp_assoc] using hh

end
end Resonance.ShiftedOperatorLimit
