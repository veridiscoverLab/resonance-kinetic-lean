import Resonance.PlaneGlobal
import Resonance.Collision
import Mathlib.Probability.Kernel.Composition.MeasureCompProd
import Mathlib.Probability.Kernel.Integral
import Mathlib.Probability.Kernel.MeasurableIntegral
import Mathlib.Probability.Kernel.Composition.IntegralCompProd

open MeasureTheory Set Metric ProbabilityTheory
open scoped ENNReal NNReal EuclideanGeometry ProbabilityTheory

namespace Resonance.CollisionFiber
noncomputable section
set_option maxHeartbeats 600000
open Resonance.PlaneCoarea Resonance.PlaneGlobal

abbrev FiberParameters := Ray × E2

def fiberBase : Measure FiberParameters := rayOne.prod (volume : Measure E2)
instance : SigmaFinite fiberBase := by unfold fiberBase; infer_instance

def fiberFour (k : E) (b : FiberParameters) : FourMomenta := planeShell (k,b) 0

theorem fiberFour_joint_measurable :
    Measurable (Function.uncurry fiberFour) := planeShell_zero_measurable

theorem fiberFour_measurable (k : E) : Measurable (fiberFour k) :=
  fiberFour_joint_measurable.comp measurable_prodMk_left

@[simp] theorem fiberFour_output (k : E) (b : FiberParameters) : fiberFour k b 0 = k := rfl

def fiberAllowed (R : ℝ) (k : E) : Set FiberParameters :=
  {b | fiberFour k b ∈ CoareaNormalization.allFourFlags R}

theorem fiberAllowed_measurable (R : ℝ) (k : E) : MeasurableSet (fiberAllowed R k) :=
  (CoareaNormalization.allFourFlags_measurable R).preimage (fiberFour_measurable k)

/-- The actual output-k fiber, with all four original flags and the same plane parameterization. -/
def fiberMeasure (R : ℝ) (k : E) : Measure FourMomenta :=
  (1/2:ℝ≥0∞) • Measure.map (fiberFour k) (fiberBase.restrict (fiberAllowed R k))

theorem fiberMeasure_apply (R : ℝ) (k : E) {s : Set FourMomenta} (hs : MeasurableSet s) :
    fiberMeasure R k s = (1/2:ℝ≥0∞) *
      fiberBase {b | fiberFour k b ∈ s ∧ fiberFour k b ∈ CoareaNormalization.allFourFlags R} := by
  rw [fiberMeasure,Measure.smul_apply,Measure.map_apply (fiberFour_measurable k) hs,
    Measure.restrict_apply ((fiberFour_measurable k) hs)]
  rfl

theorem fiberMeasure_measurable (R : ℝ) : Measurable (fiberMeasure R) := by
  apply Measure.measurable_of_measurable_coe
  intro s hs
  simp_rw [fiberMeasure_apply R _ hs]
  have hm : MeasurableSet {p : E × FiberParameters |
      fiberFour p.1 p.2 ∈ s ∧
      fiberFour p.1 p.2 ∈ CoareaNormalization.allFourFlags R} :=
    (hs.preimage fiberFour_joint_measurable).inter
      ((CoareaNormalization.allFourFlags_measurable R).preimage fiberFour_joint_measurable)
  exact measurable_const.mul (measurable_measure_prodMk_left hm)

def collisionKernel (R : ℝ) : Kernel E FourMomenta :=
  ⟨fiberMeasure R, fiberMeasure_measurable R⟩

@[simp] theorem collisionKernel_apply (R : ℝ) (k : E) :
    collisionKernel R k = fiberMeasure R k := rfl

def fiberBox (R : ℝ) : Set FiberParameters :=
  {b | (b.1.2:ℝ) ≤ 6*|R| ∧ ‖b.2‖ ≤ 6*|R|}

theorem fiberBox_measurable (R : ℝ) : MeasurableSet (fiberBox R) := by
  have h1 : MeasurableSet {b : FiberParameters | (b.1.2:ℝ) ≤ 6*|R|} :=
    measurableSet_le (by fun_prop) measurable_const
  have h2 : MeasurableSet {b : FiberParameters | ‖b.2‖ ≤ 6*|R|} :=
    measurableSet_le (by fun_prop) measurable_const
  exact h1.inter h2

theorem fiberBox_finite (R : ℝ) : fiberBase (fiberBox R) < ∞ := by
  let upper : Radius := ⟨6*|R|+1, by change 0<6*|R|+1; positivity⟩
  have hb : fiberBox R ⊆ ((univ : Set Sphere) ×ˢ Iio upper) ×ˢ
      closedBall (0:E2) (6*|R|) := by
    intro b hb
    exact ⟨⟨mem_univ _, by change (b.1.2:ℝ)<6*|R|+1; linarith [hb.1]⟩,
      by simpa [mem_closedBall,dist_zero_right] using hb.2⟩
  apply lt_of_le_of_lt (measure_mono hb)
  rw [fiberBase,Measure.prod_prod,rayOne,Measure.prod_prod]
  apply ENNReal.mul_lt_top
  · apply ENNReal.mul_lt_top (measure_lt_top _ _)
    rw [radialOne,Measure.volumeIoiPow_apply_Iio]
    exact ENNReal.ofReal_lt_top
  · exact (isCompact_closedBall (0:E2) (6*|R|)).measure_lt_top

theorem fiberAllowed_subset_box {R : ℝ} (hR : 0≤R) (k : E) :
    fiberAllowed R k ⊆ fiberBox R := by
  intro b hb
  have hh := (planeShell_flags_bounds hR (k,b) 0 hb).1
  exact ⟨by simpa [abs_of_nonneg hR] using hh.2.1,
    by simpa [abs_of_nonneg hR] using hh.2.2⟩

/-- An explicit finite geometric bound, obtained before defining any loss frequency. -/
def fiberMassBound (R : ℝ) : ℝ≥0∞ := (1/2:ℝ≥0∞) * fiberBase (fiberBox R)

theorem fiberMassBound_lt_top (R : ℝ) : fiberMassBound R < ∞ :=
  ENNReal.mul_lt_top (by norm_num) (fiberBox_finite R)

theorem fiberMeasure_mass_le {R : ℝ} (hR : 0≤R) (k : E) :
    fiberMeasure R k univ ≤ fiberMassBound R := by
  rw [fiberMeasure,Measure.smul_apply,Measure.map_apply (fiberFour_measurable k) MeasurableSet.univ,
    preimage_univ,Measure.restrict_apply_univ]
  exact mul_le_mul_right (measure_mono (fiberAllowed_subset_box hR k)) _

theorem collisionKernel_finite {R : ℝ} (hR : 0≤R) : IsFiniteKernel (collisionKernel R) :=
  ⟨⟨fiberMassBound R,fiberMassBound_lt_top R,fiberMeasure_mass_le hR⟩⟩

/-- Disintegration of the same complete four-leg measure over physical output volume. -/
theorem collisionKernel_joint_measure {R : ℝ} (hR : 0≤R) :
    Measure.map Prod.snd ((volume : Measure E) ⊗ₘ collisionKernel R) =
      ResonantMeasure.pairingMeasure R := by
  letI := collisionKernel_finite hR
  rw [← planeMeasure_eq_pairingMeasure hR]
  ext s hs
  rw [Measure.map_apply measurable_snd hs,
    Measure.compProd_apply (hs.preimage measurable_snd)]
  change (∫⁻ k : E, fiberMeasure R k s) = planeMeasure R s
  simp_rw [fiberMeasure_apply R _ hs]
  rw [planeMeasure,Measure.map_apply planeShell_zero_measurable hs,
    planeParameterMeasure,Measure.smul_apply,
    Measure.restrict_apply (hs.preimage planeShell_zero_measurable)]
  have hm : MeasurableSet ((fun p : PlaneParameters => planeShell p 0) ⁻¹' s ∩ planeAllowed R) :=
    (hs.preimage planeShell_zero_measurable).inter (planeAllowed_measurable R)
  rw [planeBase,Measure.prod_apply hm]
  exact lintegral_const_mul' (1/2:ℝ≥0∞) _ (by norm_num)

theorem fiber_support (R : ℝ) (k : E) :
    ∀ᵐ q ∂fiberMeasure R k,
      q ∈ CoareaNormalization.allFourFlags R ∧ q 0 = k := by
  unfold fiberMeasure
  apply Measure.ae_smul_measure
  have hs : MeasurableSet {q : FourMomenta |
      q ∈ CoareaNormalization.allFourFlags R ∧ q 0 = k} :=
    (CoareaNormalization.allFourFlags_measurable R).inter
      (measurableSet_eq_fun (by fun_prop) measurable_const)
  apply (ae_map_iff (fiberFour_measurable k).aemeasurable hs).2
  filter_upwards [ae_restrict_mem (fiberAllowed_measurable R k)] with b hb
  exact ⟨hb,fiberFour_output k b⟩

theorem fiberMeasure_zero_outside (R : ℝ) {k : E}
    (hk : k ∉ ResonantMeasure.cube R) : fiberMeasure R k = 0 := by
  have he : fiberAllowed R k = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro b hb
    exact hk (by simpa only [fiberFour_output] using hb 0)
  simp [fiberMeasure,he]

def collisionIntegrand (f : E → ℝ) (q : FourMomenta) : ℝ :=
  Collision.collisionPolynomial (fun i => f (q i))

theorem collisionIntegrand_measurable {f : E → ℝ} (hf : Measurable f) :
    Measurable (collisionIntegrand f) := by
  unfold collisionIntegrand Collision.collisionPolynomial
  fun_prop

theorem collisionIntegrand_bound {R M : ℝ} (hM : 0≤M) (f : E → ℝ)
    (hf : ∀ k∈ResonantMeasure.cube R, ‖f k‖≤M)
    {q : FourMomenta} (hq : q ∈ CoareaNormalization.allFourFlags R) :
    ‖collisionIntegrand f q‖ ≤ 4*M^3 := by
  have ht (i j l : Fin 4) : ‖f (q i)*f (q j)*f (q l)‖ ≤ M^3 := by
    rw [norm_mul,norm_mul]
    calc
      ‖f (q i)‖*‖f (q j)‖*‖f (q l)‖ ≤ M*M*M :=
        mul_le_mul (mul_le_mul (hf _ (hq i)) (hf _ (hq j)) (norm_nonneg _) hM)
          (hf _ (hq l)) (norm_nonneg _) (mul_nonneg hM hM)
      _ = M^3 := by ring
  unfold collisionIntegrand Collision.collisionPolynomial
  have h1 := norm_add_le (f (q 1)*f (q 2)*f (q 3)) (f (q 0)*f (q 2)*f (q 3))
  have h2 := norm_sub_le
    (f (q 1)*f (q 2)*f (q 3)+f (q 0)*f (q 2)*f (q 3)) (f (q 0)*f (q 1)*f (q 3))
  have h3 := norm_sub_le
    (f (q 1)*f (q 2)*f (q 3)+f (q 0)*f (q 2)*f (q 3)-f (q 0)*f (q 1)*f (q 3))
    (f (q 0)*f (q 1)*f (q 2))
  linarith [ht 1 2 3,ht 0 2 3,ht 0 1 3,ht 0 1 2]

theorem collisionIntegrand_integrable {R M : ℝ} (hR : 0≤R) (hM : 0≤M)
    (f : E → ℝ) (hfm : Measurable f)
    (hf : ∀ k∈ResonantMeasure.cube R, ‖f k‖≤M) (k : E) :
    Integrable (collisionIntegrand f) (fiberMeasure R k) := by
  letI := collisionKernel_finite hR
  haveI : IsFiniteMeasure (fiberMeasure R k) :=
    inferInstanceAs (IsFiniteMeasure (collisionKernel R k))
  apply (integrable_const (4*M^3)).mono' (collisionIntegrand_measurable hfm).aestronglyMeasurable
  filter_upwards [fiber_support R k] with q hq
  exact collisionIntegrand_bound hM f hf hq.1

/-- Original full cubic output on the proved physical fiber. -/
def collisionOutput (R : ℝ) (f : E → ℝ) (k : E) : ℝ :=
  ∫ q, collisionIntegrand f q ∂fiberMeasure R k

theorem collisionOutput_measurable (R : ℝ) {f : E → ℝ} (hf : Measurable f) :
    Measurable (collisionOutput R f) :=
  ((collisionIntegrand_measurable hf).stronglyMeasurable.integral_kernel
    (κ := collisionKernel R)).measurable

theorem collisionOutput_zero_outside (R : ℝ) (f : E → ℝ) {k : E}
    (hk : k ∉ ResonantMeasure.cube R) : collisionOutput R f k = 0 := by
  simp [collisionOutput,fiberMeasure_zero_outside R hk]

theorem collisionOutput_bound {R M : ℝ} (hR : 0≤R) (hM : 0≤M)
    (f : E → ℝ) (hf : ∀ k∈ResonantMeasure.cube R, ‖f k‖≤M) (k : E) :
    ‖collisionOutput R f k‖ ≤ 4*M^3*(fiberMassBound R).toReal := by
  letI := collisionKernel_finite hR
  haveI : IsFiniteMeasure (fiberMeasure R k) :=
    inferInstanceAs (IsFiniteMeasure (collisionKernel R k))
  apply le_trans (norm_integral_le_of_norm_le_const (C := 4*M^3) ?_)
  · exact mul_le_mul_of_nonneg_left
      (ENNReal.toReal_mono (fiberMassBound_lt_top R).ne (fiberMeasure_mass_le hR k))
      (by positivity)
  · filter_upwards [fiber_support R k] with q hq
    exact collisionIntegrand_bound hM f hf hq.1

theorem collisionOutput_integrable {R M : ℝ} (hR : 0≤R) (hM : 0≤M)
    (f : E → ℝ) (hfm : Measurable f)
    (hf : ∀ k∈ResonantMeasure.cube R, ‖f k‖≤M) :
    Integrable (collisionOutput R f) := by
  let C := 4*M^3*(fiberMassBound R).toReal
  have hc : Integrable ((closedBall (0:E) (3*R)).indicator (fun _ : E => C)) :=
    (integrable_indicator_iff isClosed_closedBall.measurableSet).2
      (integrableOn_const (isCompact_closedBall (0:E) (3*R)).measure_ne_top)
  apply hc.mono' (collisionOutput_measurable R hfm).aestronglyMeasurable
  apply ae_of_all
  intro k
  by_cases hk : k∈closedBall (0:E) (3*R)
  · rw [Set.indicator_of_mem hk]
    exact collisionOutput_bound hR hM f hf k
  · have hn : k∉ResonantMeasure.cube R := by
      intro h
      exact hk (by simpa [mem_closedBall,dist_zero_right] using
        ResonantMeasure.norm_le_three_R hR h)
    rw [Set.indicator_of_notMem hk,collisionOutput_zero_outside R f hn,norm_zero]

/-- Genuine Fubini over the constructed collision kernel, for the original joint measure. -/
theorem collisionKernel_joint_integral {R : ℝ} (hR : 0≤R) (Φ : FourMomenta → ℝ)
    (hΦ : Integrable Φ (ResonantMeasure.pairingMeasure R)) :
    (∫ q, Φ q ∂(ResonantMeasure.pairingMeasure R)) =
      ∫ k : E, ∫ q, Φ q ∂fiberMeasure R k := by
  letI := collisionKernel_finite hR
  have hi : Integrable Φ (Measure.map Prod.snd ((volume : Measure E) ⊗ₘ collisionKernel R)) :=
    (collisionKernel_joint_measure hR).symm ▸ hΦ
  rw [← collisionKernel_joint_measure hR,
    integral_map measurable_snd.aemeasurable hi.aestronglyMeasurable]
  exact Measure.integral_compProd (hi.comp_measurable measurable_snd)

theorem bounded_joint_integrable {R B : ℝ} (hR : 0≤R)
    (Φ : FourMomenta → ℝ) (hΦm : Measurable Φ)
    (hΦ : ∀ q∈CoareaNormalization.allFourFlags R, ‖Φ q‖≤B) :
    Integrable Φ (ResonantMeasure.pairingMeasure R) := by
  letI := ResonantMeasure.pairingMeasure_finite hR
  have ha : ∀ᵐ q ∂(ResonantMeasure.pairingMeasure R), q∈ResonantMeasure.fullResonance R :=
    ae_iff.mpr (by simpa using ResonantMeasure.pairing_supported_on_fullResonance R)
  apply (integrable_const B).mono' hΦm.aestronglyMeasurable
  filter_upwards [ha] with q hq
  exact hΦ q hq.1

/-- The complete cubic collision output has the same common-four-leg weak integral. -/
theorem collisionOutput_weak_pairing {R M B : ℝ} (hR : 0≤R) (hM : 0≤M)
    (hB : 0≤B) (f φ : E → ℝ) (hfm : Measurable f) (hφm : Measurable φ)
    (hf : ∀ k∈ResonantMeasure.cube R, ‖f k‖≤M)
    (hφ : ∀ k∈ResonantMeasure.cube R, ‖φ k‖≤B) :
    (∫ k : E, φ k * collisionOutput R f k) =
      ∫ q, φ (q 0) * collisionIntegrand f q ∂(ResonantMeasure.pairingMeasure R) := by
  have hm : Measurable (fun q : FourMomenta => φ (q 0)*collisionIntegrand f q) :=
    (hφm.comp (measurable_pi_apply 0)).mul (collisionIntegrand_measurable hfm)
  have hi := bounded_joint_integrable hR _ hm
    (B := B*(4*M^3)) (fun q hq => by
      rw [norm_mul]
      exact mul_le_mul (hφ _ (hq 0)) (collisionIntegrand_bound hM f hf hq)
        (norm_nonneg _) hB)
  rw [collisionKernel_joint_integral hR _ hi]
  apply integral_congr_ae
  apply ae_of_all
  intro k
  change φ k * (∫ q, collisionIntegrand f q ∂fiberMeasure R k) =
    ∫ q, φ (q 0) * collisionIntegrand f q ∂fiberMeasure R k
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [fiber_support R k] with q hq
  rw [hq.2]

/-! Complete declaration types and axiom audit. -/
#check fiberFour_joint_measurable
#print axioms fiberFour_joint_measurable
#check fiberFour_measurable
#print axioms fiberFour_measurable
#check fiberFour_output
#print axioms fiberFour_output
#check fiberAllowed_measurable
#print axioms fiberAllowed_measurable
#check fiberMeasure_apply
#print axioms fiberMeasure_apply
#check fiberMeasure_measurable
#print axioms fiberMeasure_measurable
#check collisionKernel_apply
#print axioms collisionKernel_apply
#check fiberBox_measurable
#print axioms fiberBox_measurable
#check fiberBox_finite
#print axioms fiberBox_finite
#check fiberAllowed_subset_box
#print axioms fiberAllowed_subset_box
#check fiberMassBound_lt_top
#print axioms fiberMassBound_lt_top
#check fiberMeasure_mass_le
#print axioms fiberMeasure_mass_le
#check collisionKernel_finite
#print axioms collisionKernel_finite
#check collisionKernel_joint_measure
#print axioms collisionKernel_joint_measure
#check fiber_support
#print axioms fiber_support
#check fiberMeasure_zero_outside
#print axioms fiberMeasure_zero_outside
#check collisionIntegrand_measurable
#print axioms collisionIntegrand_measurable
#check collisionIntegrand_bound
#print axioms collisionIntegrand_bound
#check collisionIntegrand_integrable
#print axioms collisionIntegrand_integrable
#check collisionOutput_measurable
#print axioms collisionOutput_measurable
#check collisionOutput_zero_outside
#print axioms collisionOutput_zero_outside
#check collisionOutput_bound
#print axioms collisionOutput_bound
#check collisionOutput_integrable
#print axioms collisionOutput_integrable
#check collisionKernel_joint_integral
#print axioms collisionKernel_joint_integral
#check bounded_joint_integrable
#print axioms bounded_joint_integrable
#check collisionOutput_weak_pairing
#print axioms collisionOutput_weak_pairing

end
end Resonance.CollisionFiber
