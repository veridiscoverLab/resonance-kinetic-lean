import Resonance.CollisionFrequencyPositive
import Resonance.WeightedJointMeasure

/-! The marginal density is derived from the original joint measure and the
same complete collision fibers.  This supplies the measure identity needed
to extend the full difference to its degenerating frequency-weighted space. -/
open MeasureTheory Set
open scoped ENNReal
namespace Resonance.CollisionMarginalDensity
noncomputable section
open ResonantMeasure CollisionFiber WeightedJointMeasure

def fiberDensity (R : ℝ) (w : FourMomenta → ℝ≥0∞) (k : E) : ℝ≥0∞ :=
  ∫⁻q,w q ∂fiberMeasure R k

theorem fiberDensity_measurable {R : ℝ} {w : FourMomenta → ℝ≥0∞}
    (hw : Measurable w) : Measurable (fiberDensity R w) :=
  hw.lintegral_kernel (κ := collisionKernel R)

theorem weighted_first_marginal {R : ℝ} (hR : 0≤R)
    {w : FourMomenta → ℝ≥0∞} (hw : Measurable w) :
    ((pairingMeasure R).withDensity w).map (fun q=>q 0) =
      (volume : Measure E).withDensity (fiberDensity R w) := by
  letI := collisionKernel_finite hR
  apply Measure.ext_of_lintegral
  intro f hf
  have hf0 : Measurable (fun q : FourMomenta=>f (q 0)) := by fun_prop
  rw [lintegral_map hf (measurable_pi_apply 0),
    lintegral_withDensity_eq_lintegral_mul _ hw hf0,
    lintegral_withDensity_eq_lintegral_mul _ (fiberDensity_measurable hw) hf,
    ←collisionKernel_joint_measure hR]
  simp only [Pi.mul_apply]
  rw [lintegral_map (hw.mul hf0) measurable_snd,
    Measure.lintegral_compProd (by fun_prop)]
  apply lintegral_congr
  intro k
  change (∫⁻q,w q*f (q 0)∂fiberMeasure R k)=fiberDensity R w k*f k
  calc
    _ = ∫⁻q,w q*f k∂fiberMeasure R k := by
      apply lintegral_congr_ae
      filter_upwards [fiber_support R k] with q hq
      rw [hq.2]
    _ = _ := lintegral_mul_const (f k) hw

theorem weighted_all_marginals {R : ℝ} (hR : 0≤R)
    (θ : Thermodynamics.Parameter) (i : Fin 4) :
    (jointMeasure R θ).map (fun q=>q i) =
      (volume : Measure E).withDensity (fiberDensity R (weight θ)) := by
  rw [marginal_eq_first R θ i]
  exact weighted_first_marginal hR (weight_measurable θ)

theorem fiberDensity_zero_outside (R : ℝ) (w : FourMomenta → ℝ≥0∞)
    {k : E} (hk : k∉cube R) : fiberDensity R w k=0 := by
  simp [fiberDensity,fiberMeasure_zero_outside R hk]

theorem triple_integrable {R M : ℝ} (hR : 0≤R) (hM : 0≤M)
    {N : E→ℝ} (hN : Measurable N) (hb : ∀k∈cube R,‖N k‖≤M) (k : E) :
    Integrable (fun q : FourMomenta=>N (q 1)*N (q 2)*N (q 3)) (fiberMeasure R k) := by
  letI := collisionKernel_finite hR
  letI : IsFiniteMeasure (fiberMeasure R k) :=
    inferInstanceAs (IsFiniteMeasure (collisionKernel R k))
  apply (integrable_const (M^3)).mono' (by fun_prop)
  filter_upwards [fiber_support R k] with q hq
  rw [norm_mul,norm_mul]
  calc
    _ ≤ M*M*M := mul_le_mul
      (mul_le_mul (hb _ (hq.1 1)) (hb _ (hq.1 2)) (norm_nonneg _) hM)
      (hb _ (hq.1 3)) (norm_nonneg _) (mul_nonneg hM hM)
    _ = M^3 := by ring

theorem lossFrequency_measurable (R : ℝ) {N : E→ℝ} (hN : Measurable N) :
    Measurable (CollisionFrequency.lossFrequency R N) := by
  apply hN.inv.mul
  have hm : Measurable (fun q : FourMomenta=>N (q 1)*N (q 2)*N (q 3)) := by fun_prop
  exact (hm.stronglyMeasurable.integral_kernel (κ := collisionKernel R)).measurable

/-- The exact original marginal is N² times the original loss frequency. -/
theorem weighted_density_eq_frequency {R : ℝ} (hR : 0≤R)
    {θ : Thermodynamics.Parameter} (hθ : θ∈Thermodynamics.positiveDomain R)
    {k : E} (hk : k∈cube R) :
    fiberDensity R (weight θ) k = ENNReal.ofReal
      ((profile θ k)^2*CollisionFrequency.lossFrequency R (profile θ) k) := by
  obtain ⟨M,hM,hbound⟩ := profile_bounded hθ
  have hi := triple_integrable hR hM (profile_measurable θ)
    (fun k hk=>by simpa only [Real.norm_eq_abs] using hbound k hk) k
  have hp : 0<profile θ k := profile_pos hθ hk
  have hmeas : Measurable (fun q : FourMomenta=>
      profile θ (q 1)*profile θ (q 2)*profile θ (q 3)) :=
    (((profile_measurable θ).comp (measurable_pi_apply 1)).mul
      ((profile_measurable θ).comp (measurable_pi_apply 2))).mul
      ((profile_measurable θ).comp (measurable_pi_apply 3))
  have ha : ∀ᵐq∂fiberMeasure R k,
      weight θ q=ENNReal.ofReal (profile θ k)*
        ENNReal.ofReal (profile θ (q 1)*profile θ (q 2)*profile θ (q 3)) := by
    filter_upwards [fiber_support R k] with q hq
    unfold weight
    simp only [Fin.prod_univ_succ,Fin.prod_univ_zero,mul_one,hq.2]
    change ENNReal.ofReal (profile θ k*(profile θ (q 1)*
      (profile θ (q 2)*profile θ (q 3))))=_
    rw [←ENNReal.ofReal_mul hp.le]
    congr 1
    ring
  have hnonneg : 0≤ᵐ[fiberMeasure R k]
      (fun q : FourMomenta=>profile θ (q 1)*profile θ (q 2)*profile θ (q 3)) := by
    filter_upwards [fiber_support R k] with q hq
    exact mul_nonneg (mul_nonneg (profile_pos hθ (hq.1 1)).le
      (profile_pos hθ (hq.1 2)).le) (profile_pos hθ (hq.1 3)).le
  unfold fiberDensity
  rw [lintegral_congr_ae ha,lintegral_const_mul _ hmeas.ennreal_ofReal,
    ←ofReal_integral_eq_lintegral_ofReal hi hnonneg,←ENNReal.ofReal_mul hp.le]
  congr 1
  unfold CollisionFrequency.lossFrequency FiberContinuity.fiberReadout
  field_simp [hp.ne']

theorem lossFrequency_zero_outside (R : ℝ) (N : E→ℝ) {k : E}
    (hk : k∉cube R) : CollisionFrequency.lossFrequency R N k=0 := by
  simp [CollisionFrequency.lossFrequency,FiberContinuity.fiberReadout,
    fiberMeasure_zero_outside R hk]

theorem weighted_density_eq_frequency_global {R : ℝ} (hR : 0≤R)
    {θ : Thermodynamics.Parameter} (hθ : θ∈Thermodynamics.positiveDomain R) (k : E) :
    fiberDensity R (weight θ) k = ENNReal.ofReal
      ((profile θ k)^2*CollisionFrequency.lossFrequency R (profile θ) k) := by
  by_cases hk : k∈cube R
  · exact weighted_density_eq_frequency hR hθ hk
  · simp [fiberDensity_zero_outside R _ hk,lossFrequency_zero_outside R _ hk]

def frequencyMeasure (R : ℝ) (θ : Thermodynamics.Parameter) : Measure E :=
  (volume : Measure E).withDensity
    (fun k=>ENNReal.ofReal (CollisionFrequency.lossFrequency R (profile θ) k))

theorem frequencyMeasure_sharp_cube (R : ℝ) (θ : Thermodynamics.Parameter) :
    frequencyMeasure R θ=(volume.restrict (cube R)).withDensity
      (fun k=>ENNReal.ofReal (CollisionFrequency.lossFrequency R (profile θ) k)) := by
  rw [←withDensity_indicator (FiberContinuity.cube_isClosed R).measurableSet]
  apply withDensity_congr_ae
  exact Filter.Eventually.of_forall (fun k=>by
    by_cases hk : k∈cube R
    · simp [hk]
    · simp [hk,lossFrequency_zero_outside R _ hk])

theorem weighted_all_marginals_frequency {R : ℝ} (hR : 0≤R)
    {θ : Thermodynamics.Parameter} (hθ : θ∈Thermodynamics.positiveDomain R)
    (i : Fin 4) :
    (jointMeasure R θ).map (fun q=>q i)=
      (frequencyMeasure R θ).withDensity (fun k=>ENNReal.ofReal ((profile θ k)^2)) := by
  rw [weighted_all_marginals hR θ i]
  unfold frequencyMeasure
  rw [←withDensity_mul _ (lossFrequency_measurable R (profile_measurable θ)).ennreal_ofReal
    ((profile_measurable θ).pow_const 2).ennreal_ofReal]
  apply withDensity_congr_ae
  exact Filter.Eventually.of_forall (fun k=>by
    rw [weighted_density_eq_frequency_global hR hθ]
    simp only [Pi.mul_apply]
    rw [ENNReal.ofReal_mul (sq_nonneg _),mul_comm])

end
end Resonance.CollisionMarginalDensity
