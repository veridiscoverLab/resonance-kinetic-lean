import Resonance.FiberContinuity

/-!
Gain/loss and quasipositivity for the original full sharp collision fibers.
No positivity or continuation property of an unknown evolution is assumed.
-/
open MeasureTheory Set Metric
open scoped ENNReal NNReal EuclideanGeometry

namespace Resonance.CollisionPositivity
noncomputable section
set_option maxHeartbeats 600000
open Resonance.PlaneCoarea Resonance.CollisionFiber Resonance.FiberContinuity

def gainIntegrand (f : E → ℝ) (q : FourMomenta) : ℝ :=
  f (q 2)*f (q 3)*(f (q 0)+f (q 1))

def lossIntegrand (f : E → ℝ) (q : FourMomenta) : ℝ :=
  f (q 1)*(f (q 2)+f (q 3))

theorem full_gain_loss_polynomial (f : E → ℝ) (q : FourMomenta) :
    collisionIntegrand f q = gainIntegrand f q-f (q 0)*lossIntegrand f q := by
  unfold collisionIntegrand Collision.collisionPolynomial gainIntegrand lossIntegrand
  ring

theorem gainIntegrand_measurable {f : E → ℝ} (hf : Measurable f) :
    Measurable (gainIntegrand f) := by
  unfold gainIntegrand
  fun_prop

theorem lossIntegrand_measurable {f : E → ℝ} (hf : Measurable f) :
    Measurable (lossIntegrand f) := by
  unfold lossIntegrand
  fun_prop

theorem gainIntegrand_bound {R M : ℝ} (hM : 0≤M) (f : E → ℝ)
    (hf : ∀ k∈ResonantMeasure.cube R, ‖f k‖≤M)
    {q : FourMomenta} (hq : q∈CoareaNormalization.allFourFlags R) :
    ‖gainIntegrand f q‖≤2*M^3 := by
  unfold gainIntegrand
  rw [norm_mul,norm_mul]
  calc
    _ ≤ M*M*(M+M) := by
      gcongr
      · exact hf _ (hq 2)
      · exact hf _ (hq 3)
      · exact (norm_add_le _ _).trans (add_le_add (hf _ (hq 0)) (hf _ (hq 1)))
    _ = 2*M^3 := by ring

theorem lossIntegrand_bound {R M : ℝ} (hM : 0≤M) (f : E → ℝ)
    (hf : ∀ k∈ResonantMeasure.cube R, ‖f k‖≤M)
    {q : FourMomenta} (hq : q∈CoareaNormalization.allFourFlags R) :
    ‖lossIntegrand f q‖≤2*M^2 := by
  unfold lossIntegrand
  rw [norm_mul]
  calc
    _ ≤ M*(M+M) := by
      gcongr
      · exact hf _ (hq 1)
      · exact (norm_add_le _ _).trans (add_le_add (hf _ (hq 2)) (hf _ (hq 3)))
    _ = 2*M^2 := by ring

theorem fiber_integrable_of_bounded {R B : ℝ} (hR : 0≤R)
    (Φ : FourMomenta → ℝ) (hΦm : Measurable Φ)
    (hΦ : ∀ q∈CoareaNormalization.allFourFlags R, ‖Φ q‖≤B) (k : E) :
    Integrable Φ (fiberMeasure R k) := by
  letI := collisionKernel_finite hR
  haveI : IsFiniteMeasure (fiberMeasure R k) :=
    inferInstanceAs (IsFiniteMeasure (collisionKernel R k))
  apply (integrable_const B).mono' hΦm.aestronglyMeasurable
  filter_upwards [fiber_support R k] with q hq
  exact hΦ q hq.1

theorem gainIntegrand_integrable {R M : ℝ} (hR : 0≤R) (hM : 0≤M)
    (f : E → ℝ) (hfm : Measurable f)
    (hf : ∀ k∈ResonantMeasure.cube R, ‖f k‖≤M) (k : E) :
    Integrable (gainIntegrand f) (fiberMeasure R k) :=
  fiber_integrable_of_bounded hR _ (gainIntegrand_measurable hfm)
    (fun _ hq => gainIntegrand_bound hM f hf hq) k

theorem lossIntegrand_integrable {R M : ℝ} (hR : 0≤R) (hM : 0≤M)
    (f : E → ℝ) (hfm : Measurable f)
    (hf : ∀ k∈ResonantMeasure.cube R, ‖f k‖≤M) (k : E) :
    Integrable (lossIntegrand f) (fiberMeasure R k) :=
  fiber_integrable_of_bounded hR _ (lossIntegrand_measurable hfm)
    (fun _ hq => lossIntegrand_bound hM f hf hq) k

def gainOutput (R : ℝ) (f : E → ℝ) (k : E) : ℝ :=
  ∫ q, gainIntegrand f q ∂fiberMeasure R k

def lossOutput (R : ℝ) (f : E → ℝ) (k : E) : ℝ :=
  ∫ q, lossIntegrand f q ∂fiberMeasure R k

/-- The output leg is the same k in the original fiber, not an averaged replacement. -/
theorem collisionOutput_gain_loss {R M : ℝ} (hR : 0≤R) (hM : 0≤M)
    (f : E → ℝ) (hfm : Measurable f)
    (hf : ∀ k∈ResonantMeasure.cube R, ‖f k‖≤M) (k : E) :
    collisionOutput R f k=gainOutput R f k-f k*lossOutput R f k := by
  rw [collisionOutput,gainOutput,lossOutput,← integral_const_mul,
    ← integral_sub (gainIntegrand_integrable hR hM f hfm hf k)
      ((lossIntegrand_integrable hR hM f hfm hf k).const_mul (f k))]
  apply integral_congr_ae
  filter_upwards [fiber_support R k] with q hq
  rw [full_gain_loss_polynomial,hq.2]

theorem gainOutput_nonneg {R : ℝ} (f : E → ℝ)
    (hf : ∀ k∈ResonantMeasure.cube R, 0≤f k) (k : E) :
    0≤gainOutput R f k := by
  apply integral_nonneg_of_ae
  filter_upwards [fiber_support R k] with q hq
  exact mul_nonneg (mul_nonneg (hf _ (hq.1 2)) (hf _ (hq.1 3)))
    (add_nonneg (hf _ (hq.1 0)) (hf _ (hq.1 1)))

theorem lossOutput_nonneg {R : ℝ} (f : E → ℝ)
    (hf : ∀ k∈ResonantMeasure.cube R, 0≤f k) (k : E) :
    0≤lossOutput R f k := by
  apply integral_nonneg_of_ae
  filter_upwards [fiber_support R k] with q hq
  exact mul_nonneg (hf _ (hq.1 1)) (add_nonneg (hf _ (hq.1 2)) (hf _ (hq.1 3)))

theorem gainOutput_norm_le {R M : ℝ} (hR : 0≤R) (hM : 0≤M)
    (f : E → ℝ) (hf : ∀ k∈ResonantMeasure.cube R, ‖f k‖≤M) (k : E) :
    ‖gainOutput R f k‖ ≤ 2*M^3*(fiberMassBound R).toReal := by
  letI := collisionKernel_finite hR
  haveI : IsFiniteMeasure (fiberMeasure R k) :=
    inferInstanceAs (IsFiniteMeasure (collisionKernel R k))
  apply le_trans (norm_integral_le_of_norm_le_const (C := 2*M^3) ?_)
  · exact mul_le_mul_of_nonneg_left
      (ENNReal.toReal_mono (fiberMassBound_lt_top R).ne (fiberMeasure_mass_le hR k))
      (by positivity)
  · filter_upwards [fiber_support R k] with q hq
    exact gainIntegrand_bound hM f hf hq.1

theorem lossOutput_norm_le {R M : ℝ} (hR : 0≤R) (hM : 0≤M)
    (f : E → ℝ) (hf : ∀ k∈ResonantMeasure.cube R, ‖f k‖≤M) (k : E) :
    ‖lossOutput R f k‖ ≤ 2*M^2*(fiberMassBound R).toReal := by
  letI := collisionKernel_finite hR
  haveI : IsFiniteMeasure (fiberMeasure R k) :=
    inferInstanceAs (IsFiniteMeasure (collisionKernel R k))
  apply le_trans (norm_integral_le_of_norm_le_const (C := 2*M^2) ?_)
  · exact mul_le_mul_of_nonneg_left
      (ENNReal.toReal_mono (fiberMassBound_lt_top R).ne (fiberMeasure_mass_le hR k))
      (by positivity)
  · filter_upwards [fiber_support R k] with q hq
    exact lossIntegrand_bound hM f hf hq.1

/-- The pointwise lower bound used for positivity of the genuine IVP. -/
theorem collisionOutput_lower_bound {R M : ℝ} (hR : 0≤R) (hM : 0≤M)
    (f : E → ℝ) (hfm : Measurable f)
    (hf0 : ∀ k∈ResonantMeasure.cube R, 0≤f k)
    (hfM : ∀ k∈ResonantMeasure.cube R, f k≤M)
    {k : E} (hk : k∈ResonantMeasure.cube R) :
    -(2*(fiberMassBound R).toReal*M^2)*f k ≤ collisionOutput R f k := by
  have hb : ∀ p∈ResonantMeasure.cube R, ‖f p‖≤M := by
    intro p hp
    simpa [Real.norm_eq_abs,abs_of_nonneg (hf0 p hp)] using hfM p hp
  rw [collisionOutput_gain_loss hR hM f hfm hb k]
  have hl : lossOutput R f k≤2*M^2*(fiberMassBound R).toReal :=
    (le_abs_self _).trans (lossOutput_norm_le hR hM f hb k)
  have hp := mul_le_mul_of_nonneg_left hl (hf0 k hk)
  have hg := gainOutput_nonneg f hf0 k
  nlinarith

theorem collisionMap_lower_bound {R M : ℝ} (hR : 0≤R) (hM : 0≤M)
    (f : C(ResonantMeasure.cube R,ℝ)) (hf0 : ∀ k,0≤f k) (hfM : ‖f‖≤M)
    (k : ResonantMeasure.cube R) :
    -(2*(fiberMassBound R).toReal*M^2)*f k ≤ collisionMap R hR f k := by
  have h0 : ∀ p∈ResonantMeasure.cube R, 0≤continuousExtension R f p := by
    intro p hp
    rw [continuousExtension_eq R f ⟨p,hp⟩]
    exact hf0 _
  have hM' : ∀ p∈ResonantMeasure.cube R, continuousExtension R f p≤M := by
    intro p hp
    rw [continuousExtension_eq R f ⟨p,hp⟩]
    exact (le_abs_self _).trans ((f.norm_coe_le_norm ⟨p,hp⟩).trans hfM)
  have h := collisionOutput_lower_bound hR hM _
    (continuousExtension R f).continuous.measurable h0 hM' k.property
  rw [continuousExtension_eq R f k] at h
  exact h

theorem collisionMap_quasipositive {R : ℝ} (hR : 0≤R)
    (f : C(ResonantMeasure.cube R,ℝ)) (hf : ∀ k,0≤f k)
    {k : ResonantMeasure.cube R} (hk : f k=0) : 0≤collisionMap R hR f k := by
  simpa [hk] using collisionMap_lower_bound hR (norm_nonneg f) f hf le_rfl k

/-- The damped Picard vector field preserves the positive cone on each norm ball. -/
theorem collisionMap_shift_nonnegative {R M : ℝ} (hR : 0≤R) (hM : 0≤M)
    (f : C(ResonantMeasure.cube R,ℝ)) (hf0 : ∀ k,0≤f k) (hfM : ‖f‖≤M)
    (k : ResonantMeasure.cube R) :
    0 ≤ (collisionMap R hR f+(2*(fiberMassBound R).toReal*M^2) • f) k := by
  change 0≤collisionMap R hR f k+(2*(fiberMassBound R).toReal*M^2)*f k
  have h := collisionMap_lower_bound hR hM f hf0 hfM k
  linarith

theorem gainOutput_continuousOn {R : ℝ} (hR : 0≤R)
    (f : E → ℝ) (hf : Continuous f) :
    ContinuousOn (gainOutput R f) (ResonantMeasure.cube R) := by
  apply fiberReadout_continuousOn hR (gainIntegrand f)
  unfold gainIntegrand
  fun_prop

theorem lossOutput_continuousOn {R : ℝ} (hR : 0≤R)
    (f : E → ℝ) (hf : Continuous f) :
    ContinuousOn (lossOutput R f) (ResonantMeasure.cube R) := by
  apply fiberReadout_continuousOn hR (lossIntegrand f)
  unfold lossIntegrand
  fun_prop

/-- At every fixed output, energy conservation follows from the actual plane map. -/
theorem fiber_energy_zero (R : ℝ) (k : E) :
    ∀ᵐ q ∂fiberMeasure R k, CoareaNormalization.energy q=0 := by
  unfold fiberMeasure
  apply Measure.ae_smul_measure
  have hs : MeasurableSet {q : FourMomenta | CoareaNormalization.energy q=0} :=
    measurableSet_eq_fun CoareaNormalization.energy_continuous.measurable measurable_const
  apply (ae_map_iff (fiberFour_measurable k).aemeasurable hs).2
  exact ae_of_all _ (fun b => PlaneGlobal.planeShell_energy (k,b) 0)

def uniformRJ (μ : ℝ) (k : E) : ℝ := (μ+‖k‖^2)⁻¹

theorem uniformRJ_positive {μ : ℝ} (hμ : 0<μ) (k : E) : 0<uniformRJ μ k := by
  unfold uniformRJ
  positivity

theorem uniformRJ_bound {μ : ℝ} (hμ : 0<μ) (k : E) : uniformRJ μ k≤μ⁻¹ := by
  unfold uniformRJ
  exact (inv_le_inv₀ (by positivity : 0<μ+‖k‖^2) hμ).mpr
    (le_add_of_nonneg_right (sq_nonneg ‖k‖))

theorem uniformRJ_continuous {μ : ℝ} (hμ : 0<μ) : Continuous (uniformRJ μ) := by
  apply Continuous.inv₀
  · fun_prop
  · intro k
    positivity

theorem uniformRJ_integrand_zero {μ : ℝ} (hμ : 0<μ)
    {q : FourMomenta} (hq : CoareaNormalization.energy q=0) :
    collisionIntegrand (uniformRJ μ) q=0 := by
  rw [collisionIntegrand,Collision.collision_reciprocal_identity _
    (fun i => ne_of_gt (uniformRJ_positive hμ (q i)))]
  have he : Collision.delta (fun i => (uniformRJ μ (q i))⁻¹)=CoareaNormalization.energy q := by
    simp only [uniformRJ,inv_inv,Collision.delta,CoareaNormalization.energy]
    ring
  rw [he,hq,mul_zero]

theorem uniformRJ_collisionOutput_zero (R : ℝ) {μ : ℝ} (hμ : 0<μ) (k : E) :
    collisionOutput R (uniformRJ μ) k=0 := by
  apply integral_eq_zero_of_ae
  filter_upwards [fiber_energy_zero R k] with q hq
  exact uniformRJ_integrand_zero hμ hq

/-- The spatially uniform positive RJ profile in the same original Banach space. -/
def uniformRJMap (R μ : ℝ) (hμ : 0<μ) : C(ResonantMeasure.cube R,ℝ) :=
  ⟨fun k => uniformRJ μ k,(uniformRJ_continuous hμ).comp continuous_subtype_val⟩

theorem uniformRJMap_positive (R : ℝ) {μ : ℝ} (hμ : 0<μ)
    (k : ResonantMeasure.cube R) : 0<uniformRJMap R μ hμ k :=
  uniformRJ_positive hμ k

/-- Exact stationarity is pointwise, including every cube boundary point. -/
theorem uniformRJMap_stationary {R μ : ℝ} (hR : 0≤R) (hμ : 0<μ) :
    collisionMap R hR (uniformRJMap R μ hμ)=0 := by
  ext k
  rw [collisionMap_apply R hR _ (uniformRJ μ) (fun _ => rfl)]
  exact uniformRJ_collisionOutput_zero R hμ k

theorem fiber_momentum_zero (R : ℝ) (k : E) :
    ∀ᵐ q ∂fiberMeasure R k, q 0+q 1-q 2-q 3=0 := by
  unfold fiberMeasure
  apply Measure.ae_smul_measure
  have hs : MeasurableSet {q : FourMomenta | q 0+q 1-q 2-q 3=(0:E)} :=
    measurableSet_eq_fun (by fun_prop) measurable_const
  apply (ae_map_iff (fiberFour_measurable k).aemeasurable hs).2
  apply ae_of_all
  intro b
  rw [fiberFour_output,fiberFour_one,fiberFour_two,fiberFour_three]
  abel

/-- The full five-parameter reciprocal profile, in actual Euclidean momentum. -/
def rjReciprocal (α : ℝ) (β : E) (γ : ℝ) (k : E) : ℝ :=
  α+inner ℝ β k+γ*‖k‖^2

def rjProfile (α : ℝ) (β : E) (γ : ℝ) (k : E) : ℝ :=
  (rjReciprocal α β γ k)⁻¹

theorem rjReciprocal_continuous (α : ℝ) (β : E) (γ : ℝ) :
    Continuous (rjReciprocal α β γ) := by
  unfold rjReciprocal
  fun_prop

theorem rjReciprocal_full_difference (α : ℝ) (β : E) (γ : ℝ) (q : FourMomenta) :
    Collision.delta (fun i => rjReciprocal α β γ (q i)) =
      inner ℝ β (q 0+q 1-q 2-q 3)+γ*CoareaNormalization.energy q := by
  simp only [Collision.delta,rjReciprocal,CoareaNormalization.energy,inner_add_right,inner_sub_right]
  ring

/-- Detailed balance is integrated over each original fixed-output fiber. -/
theorem rjProfile_collisionOutput_zero (R α : ℝ) (β : E) (γ : ℝ)
    (hp : ∀ k∈ResonantMeasure.cube R, 0<rjReciprocal α β γ k) (k : E) :
    collisionOutput R (rjProfile α β γ) k=0 := by
  apply integral_eq_zero_of_ae
  filter_upwards [fiber_support R k,fiber_energy_zero R k,fiber_momentum_zero R k] with q hq he hm
  have hn : ∀ i, rjProfile α β γ (q i)≠0 :=
    fun i => inv_ne_zero (ne_of_gt (hp _ (hq.1 i)))
  rw [collisionIntegrand,Collision.collision_reciprocal_identity _ hn]
  have hi : Collision.delta (fun i => (rjProfile α β γ (q i))⁻¹)=0 := by
    simp only [rjProfile,inv_inv]
    rw [rjReciprocal_full_difference,hm,he,inner_zero_right,mul_zero,add_zero]
  rw [hi,mul_zero]
  rfl

def rjMap (R α : ℝ) (β : E) (γ : ℝ)
    (hp : ∀ k∈ResonantMeasure.cube R, 0<rjReciprocal α β γ k) :
    C(ResonantMeasure.cube R,ℝ) :=
  ⟨fun k => rjProfile α β γ k,
    continuousOn_iff_continuous_restrict.mp
      ((rjReciprocal_continuous α β γ).continuousOn.inv₀
        (fun k hk => ne_of_gt (hp k hk)))⟩

theorem rjMap_positive (R α : ℝ) (β : E) (γ : ℝ)
    (hp : ∀ k∈ResonantMeasure.cube R, 0<rjReciprocal α β γ k)
    (k : ResonantMeasure.cube R) : 0<rjMap R α β γ hp k :=
  inv_pos.mpr (hp k k.property)

/-- Every fixed positive five-parameter RJ profile is an exact stationary collision state. -/
theorem rjMap_stationary {R : ℝ} (hR : 0≤R) (α : ℝ) (β : E) (γ : ℝ)
    (hp : ∀ k∈ResonantMeasure.cube R, 0<rjReciprocal α β γ k) :
    collisionMap R hR (rjMap R α β γ hp)=0 := by
  ext k
  rw [collisionMap_apply R hR _ (rjProfile α β γ) (fun _ => rfl)]
  exact rjProfile_collisionOutput_zero R α β γ hp k

/-! Complete theorem-type and logical-dependency audit. -/
#check full_gain_loss_polynomial
#print axioms full_gain_loss_polynomial
#check gainIntegrand_measurable
#print axioms gainIntegrand_measurable
#check lossIntegrand_measurable
#print axioms lossIntegrand_measurable
#check gainIntegrand_bound
#print axioms gainIntegrand_bound
#check lossIntegrand_bound
#print axioms lossIntegrand_bound
#check fiber_integrable_of_bounded
#print axioms fiber_integrable_of_bounded
#check gainIntegrand_integrable
#print axioms gainIntegrand_integrable
#check lossIntegrand_integrable
#print axioms lossIntegrand_integrable
#check collisionOutput_gain_loss
#print axioms collisionOutput_gain_loss
#check gainOutput_nonneg
#print axioms gainOutput_nonneg
#check lossOutput_nonneg
#print axioms lossOutput_nonneg
#check gainOutput_norm_le
#print axioms gainOutput_norm_le
#check lossOutput_norm_le
#print axioms lossOutput_norm_le
#check collisionOutput_lower_bound
#print axioms collisionOutput_lower_bound
#check collisionMap_lower_bound
#print axioms collisionMap_lower_bound
#check collisionMap_quasipositive
#print axioms collisionMap_quasipositive
#check collisionMap_shift_nonnegative
#print axioms collisionMap_shift_nonnegative
#check gainOutput_continuousOn
#print axioms gainOutput_continuousOn
#check lossOutput_continuousOn
#print axioms lossOutput_continuousOn
#check fiber_energy_zero
#print axioms fiber_energy_zero
#check uniformRJ_positive
#print axioms uniformRJ_positive
#check uniformRJ_bound
#print axioms uniformRJ_bound
#check uniformRJ_continuous
#print axioms uniformRJ_continuous
#check uniformRJ_integrand_zero
#print axioms uniformRJ_integrand_zero
#check uniformRJ_collisionOutput_zero
#print axioms uniformRJ_collisionOutput_zero
#check uniformRJMap_positive
#print axioms uniformRJMap_positive
#check uniformRJMap_stationary
#print axioms uniformRJMap_stationary
#check fiber_momentum_zero
#print axioms fiber_momentum_zero
#check rjReciprocal_continuous
#print axioms rjReciprocal_continuous
#check rjReciprocal_full_difference
#print axioms rjReciprocal_full_difference
#check rjProfile_collisionOutput_zero
#print axioms rjProfile_collisionOutput_zero
#check rjMap_positive
#print axioms rjMap_positive
#check rjMap_stationary
#print axioms rjMap_stationary

end
end Resonance.CollisionPositivity
