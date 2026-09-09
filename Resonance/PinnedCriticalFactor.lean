import Resonance.PinnedCriticalGeometry
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.MeasureTheory.Integral.Prod

/-! The genuine shared double-difference factor, integrated over a fixed unit
square. Compact domination proves its parameter regularity before it is used
as a coordinate near a critical quartet. -/
open Real Set MeasureTheory
open scoped ContDiff Topology ENNReal
namespace Resonance.PinnedCriticalFactor
noncomputable section
open Resonance.PinnedGeometry Resonance.PinnedMeasure

def unitBox : Set (ℝ×ℝ) := Icc (0,0) (1,1)

def argumentLinear (q : ℝ×ℝ) : Ambient →L[ℝ] ℝ :=
  coordinateProjection 0+q.1 • coordinateProjection 1+q.2 • coordinateProjection 2

theorem argumentLinear_apply (q : ℝ×ℝ) (p : Ambient) :
    argumentLinear q p=p 0+q.1*p 1+q.2*p 2 := rfl

theorem argumentLinear_continuous : Continuous argumentLinear := by
  unfold argumentLinear
  fun_prop

theorem argument_joint_continuous :
    Continuous (fun p : Ambient×(ℝ×ℝ) => argumentLinear p.2 p.1) := by
  exact (argumentLinear_continuous.comp continuous_snd).clm_apply continuous_fst

def squareAverage (f : ℝ→ℝ) (p : Ambient) : ℝ :=
  ∫ q in unitBox, f (argumentLinear q p)

def squareDerivative (fp : ℝ→ℝ) (p : Ambient) : Ambient →L[ℝ] ℝ :=
  ∫ q in unitBox, fp (argumentLinear q p) • argumentLinear q

theorem squareAverage_continuous {f : ℝ→ℝ} (hf : Continuous f) :
    Continuous (squareAverage f) := by
  exact continuous_parametric_integral_of_continuous
    (f := fun p q => f (argumentLinear q p)) (μ := volume)
    (hf.comp argument_joint_continuous) (isCompact_Icc : IsCompact unitBox)

theorem derivative_integrand_joint_continuous {fp : ℝ→ℝ} (hp : Continuous fp) :
    Continuous (fun p : Ambient×(ℝ×ℝ) =>
      fp (argumentLinear p.2 p.1) • argumentLinear p.2) := by
  exact (hp.comp argument_joint_continuous).smul
    (argumentLinear_continuous.comp continuous_snd)

theorem squareDerivative_continuous {fp : ℝ→ℝ} (hp : Continuous fp) :
    Continuous (squareDerivative fp) := by
  exact continuous_parametric_integral_of_continuous
    (f := fun p q => fp (argumentLinear q p) • argumentLinear q) (μ := volume)
    (derivative_integrand_joint_continuous hp) (isCompact_Icc : IsCompact unitBox)

theorem squareAverage_hasFDerivAt {f fp : ℝ→ℝ}
    (hf : ∀t, HasDerivAt f (fp t) t) (hp : Continuous fp) (p : Ambient) :
    HasFDerivAt (squareAverage f) (squareDerivative fp p) p := by
  have hc : Continuous f := continuous_iff_continuousAt.mpr (fun t => (hf t).continuousAt)
  have hJ := derivative_integrand_joint_continuous hp
  obtain ⟨C,hC⟩ := ((isCompact_closedBall p 1).prod
    (isCompact_Icc : IsCompact unitBox)).bddAbove_image hJ.norm.continuousOn
  letI : IsFiniteMeasure ((volume : Measure (ℝ×ℝ)).restrict unitBox) :=
    ⟨by simpa using (isCompact_Icc : IsCompact unitBox).measure_lt_top (μ := volume)⟩
  apply hasFDerivAt_integral_of_dominated_of_fderiv_le
    (s := Metric.closedBall p 1) (bound := fun _ => C)
    (F' := fun p q => fp (argumentLinear q p) • argumentLinear q)
    (Metric.closedBall_mem_nhds p (by norm_num))
  · filter_upwards [] with p
    exact (hc.comp (argumentLinear_continuous.clm_apply continuous_const)).aestronglyMeasurable
  · exact (hc.comp (argumentLinear_continuous.clm_apply continuous_const)).integrableOn_Icc
  · exact (hJ.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem (μ := volume) (s := unitBox) measurableSet_Icc] with q hq
    intro p hp
    exact hC ⟨(p,q),⟨hp,hq⟩,rfl⟩
  · exact integrable_const C
  · filter_upwards [] with q
    intro p _
    exact (hf (argumentLinear q p)).comp_hasFDerivAt p (argumentLinear q).hasFDerivAt

theorem squareAverage_contDiff_one {f fp : ℝ→ℝ}
    (hf : ∀t, HasDerivAt f (fp t) t) (hp : Continuous fp) :
    ContDiff ℝ 1 (squareAverage f) := by
  exact contDiff_one_iff_hasFDerivAt.mpr
    ⟨squareDerivative fp,squareDerivative_continuous hp,squareAverage_hasFDerivAt hf hp⟩

theorem squareAverage_eq_iterated {f : ℝ→ℝ} (hf : Continuous f) (p : Ambient) :
    squareAverage f p=∫ s in (0:ℝ)..1, ∫ t in (0:ℝ)..1,
      f (p 0+s*p 1+t*p 2) := by
  have hset : unitBox=Icc (0:ℝ) 1 ×ˢ Icc (0:ℝ) 1 := by
    ext q
    change ((0≤q.1 ∧ 0≤q.2) ∧ (q.1≤1 ∧ q.2≤1)) ↔
      ((0≤q.1 ∧ q.1≤1) ∧ (0≤q.2 ∧ q.2≤1))
    tauto
  have hi : IntegrableOn (fun q : ℝ×ℝ => f (argumentLinear q p)) unitBox :=
    (hf.comp (argumentLinear_continuous.clm_apply continuous_const)).integrableOn_Icc
  unfold squareAverage
  rw [hset] at hi ⊢
  change (∫ q in Icc (0:ℝ) 1 ×ˢ Icc (0:ℝ) 1,
    f (argumentLinear q p) ∂(volume.prod volume)) = _
  rw [setIntegral_prod _ hi]
  simp only [intervalIntegral.integral_of_le (zero_le_one : (0:ℝ)≤1),
    integral_Icc_eq_integral_Ioc]
  rfl

theorem squareAverage_shared_factor {f : ℝ→ℝ} (hf : ContDiff ℝ 2 f) (z u v : ℝ) :
    Collision.rectangleDifference f z u v=
      -u*v*squareAverage (deriv (deriv f)) (WithLp.toLp 2 ![z,u,v]) := by
  have hcont : Continuous (deriv (deriv f)) := by
    have h1 : ContDiff ℝ 1 (deriv f) := hf.deriv'
    exact h1.continuous_deriv (by norm_num)
  rw [squareAverage_eq_iterated hcont]
  exact Collision.rectangle_shared_factor hf z u v

theorem squareAverage_zero_increments {f : ℝ→ℝ} (hf : Continuous f) (z : ℝ) :
    squareAverage f (WithLp.toLp 2 ![z,0,0])=f z := by
  rw [squareAverage_eq_iterated hf]
  simp

theorem squareAverage_zero_first_increment {f : ℝ→ℝ} (hf : Continuous f) (z v : ℝ) :
    squareAverage f (WithLp.toLp 2 ![z,0,v])=
      ∫ t in (0:ℝ)..1, f (z+t*v) := by
  rw [squareAverage_eq_iterated hf]
  simp

theorem squareAverage_derivative_zero_first {f fp : ℝ→ℝ}
    (hf : ∀t, HasDerivAt f (fp t) t) (hp : Continuous fp) (z v : ℝ) :
    v*squareAverage fp (WithLp.toLp 2 ![z,0,v])=f (z+v)-f z := by
  rw [squareAverage_zero_first_increment hp]
  exact (Collision.affine_increment hf hp z v).symm

theorem squareDerivative_first_vector {fp : ℝ→ℝ} (hp : Continuous fp) (p : Ambient) :
    squareDerivative fp p (WithLp.toLp 2 ![1,0,0])=squareAverage fp p := by
  have hi : IntegrableOn (fun q : ℝ×ℝ => fp (argumentLinear q p) • argumentLinear q) unitBox :=
    ((derivative_integrand_joint_continuous hp).comp
      (continuous_const.prodMk continuous_id)).integrableOn_Icc
  unfold squareDerivative squareAverage
  rw [ContinuousLinearMap.integral_apply hi]
  apply integral_congr_ae
  filter_upwards [] with q
  simp [argumentLinear,coordinateProjection]

theorem parameter_z_hasDerivAt (z u v : ℝ) :
    HasDerivAt (fun t : ℝ => WithLp.toLp 2 ![t,u,v])
      (WithLp.toLp 2 ![1,0,0] : Ambient) z := by
  have h := ((hasDerivAt_id z).smul_const
    (WithLp.toLp 2 ![1,0,0] : Ambient)).add_const (WithLp.toLp 2 ![0,u,v])
  convert h using 1
  · ext t i
    fin_cases i <;> simp
  · simp

theorem squareAverage_z_hasDerivAt {f fp : ℝ→ℝ}
    (hf : ∀t, HasDerivAt f (fp t) t) (hp : Continuous fp) (z u v : ℝ) :
    HasDerivAt (fun t : ℝ => squareAverage f (WithLp.toLp 2 ![t,u,v]))
      (squareAverage fp (WithLp.toLp 2 ![z,u,v])) z := by
  have h := (squareAverage_hasFDerivAt hf hp (WithLp.toLp 2 ![z,u,v])).comp_hasDerivAt z
    (parameter_z_hasDerivAt z u v)
  simpa only [squareDerivative_first_vector hp] using h

def sharedFactor (d : ℝ) : Ambient→ℝ := squareAverage (deriv (velocity d))

theorem sharedFactor_contDiff_one {d : ℝ} (hd0 : 0<d) (hdU : d<1/2) :
    ContDiff ℝ 1 (sharedFactor d) := by
  have h1 : ContDiff ℝ 1 (deriv (velocity d)) :=
    (PinnedClassification.velocity_contDiff hd0 hdU 2).deriv'
  exact squareAverage_contDiff_one
    (fun x => (h1.differentiable (by norm_num) x).hasDerivAt)
    (h1.continuous_deriv (by norm_num))

theorem pinned_energy_shared_factor {d : ℝ} (hd0 : 0<d) (hdU : d<1/2) (z u v : ℝ) :
    energyDefect d (z+u) (z+v) z=
      -u*v*sharedFactor d (WithLp.toLp 2 ![z,u,v]) := by
  have hdL : -(1/2:ℝ)<d := by linarith
  have he : deriv (omega d)=velocity d := funext (omega_deriv hdL hdU)
  have h := squareAverage_shared_factor (PinnedCharts.signed_omega_contDiff hdL hdU 2) z u v
  rw [he] at h
  have hw : z+u+(z+v)-z=z+u+v := by ring
  simpa only [energyDefect,Collision.rectangleDifference,hw] using h

theorem sharedFactor_at_origin {d : ℝ} (hd0 : 0<d) (hdU : d<1/2) (z : ℝ) :
    sharedFactor d (WithLp.toLp 2 ![z,0,0])=deriv (velocity d) z := by
  exact squareAverage_zero_increments
    ((PinnedClassification.velocity_contDiff hd0 hdU 1).continuous_deriv (by norm_num)) z

theorem sharedFactor_separated {d : ℝ} (hd0 : 0<d) (hdU : d<1/2) (z v : ℝ) :
    v*sharedFactor d (WithLp.toLp 2 ![z,0,v])=velocity d (z+v)-velocity d z := by
  have h1 := PinnedClassification.velocity_contDiff hd0 hdU 1
  exact squareAverage_derivative_zero_first
    (fun x => (h1.differentiable (by norm_num) x).hasDerivAt)
    (h1.continuous_deriv (by norm_num)) z v

theorem sharedFactor_z_hasDerivAt {d : ℝ} (hd0 : 0<d) (hdU : d<1/2) (z u v : ℝ) :
    HasDerivAt (fun t : ℝ => sharedFactor d (WithLp.toLp 2 ![t,u,v]))
      (squareAverage (deriv (deriv (velocity d))) (WithLp.toLp 2 ![z,u,v])) z := by
  have h1 : ContDiff ℝ 1 (deriv (velocity d)) :=
    (PinnedClassification.velocity_contDiff hd0 hdU 2).deriv'
  exact squareAverage_z_hasDerivAt
    (fun x => (h1.differentiable (by norm_num) x).hasDerivAt)
    (h1.continuous_deriv (by norm_num)) z u v

theorem sharedFactor_z_separated {d : ℝ} (hd0 : 0<d) (hdU : d<1/2) (z v : ℝ) :
    v*deriv (fun t : ℝ => sharedFactor d (WithLp.toLp 2 ![t,0,v])) z=
      deriv (velocity d) (z+v)-deriv (velocity d) z := by
  rw [(sharedFactor_z_hasDerivAt hd0 hdU z 0 v).deriv]
  have h1 : ContDiff ℝ 1 (deriv (velocity d)) :=
    (PinnedClassification.velocity_contDiff hd0 hdU 2).deriv'
  exact squareAverage_derivative_zero_first
    (fun x => (h1.differentiable (by norm_num) x).hasDerivAt)
    (h1.continuous_deriv (by norm_num)) z v

theorem sharedFactor_z_origin {d : ℝ} (hd0 : 0<d) (hdU : d<1/2) (z : ℝ) :
    deriv (fun t : ℝ => sharedFactor d (WithLp.toLp 2 ![t,0,0])) z=
      deriv (deriv (velocity d)) z := by
  rw [(sharedFactor_z_hasDerivAt hd0 hdU z 0 0).deriv]
  have h1 : ContDiff ℝ 1 (deriv (velocity d)) :=
    (PinnedClassification.velocity_contDiff hd0 hdU 2).deriv'
  exact squareAverage_zero_increments (h1.continuous_deriv (by norm_num)) z

theorem sharedFactor_separated_noncritical {d z v : ℝ}
    (hd0 : 0<d) (hdU : d<1/2)
    (hv : velocity d (z+v)=velocity d z) (hc : cos (z+v)≠cos z) :
    sharedFactor d (WithLp.toLp 2 ![z,0,v])=0 ∧
    deriv (fun t : ℝ => sharedFactor d (WithLp.toLp 2 ![t,0,v])) z≠0 := by
  have hv0 : v≠0 := by intro he; simp [he] at hc
  have hG := sharedFactor_separated hd0 hdU z v
  rw [hv,sub_self] at hG
  refine ⟨(mul_eq_zero.mp hG).resolve_left hv0,?_⟩
  intro hz
  have he := sharedFactor_z_separated hd0 hdU z v
  rw [hz,mul_zero] at he
  exact PinnedCriticalGeometry.equal_velocity_curvatures_ne hd0 hdU hv hc
    (sub_eq_zero.mp he.symm)

theorem sharedFactor_origin_alternative {d : ℝ}
    (hd0 : 0<d) (hdU : d<1/2) (z : ℝ) :
    sharedFactor d (WithLp.toLp 2 ![z,0,0])≠0 ∨
    deriv (fun t : ℝ => sharedFactor d (WithLp.toLp 2 ![t,0,0])) z≠0 := by
  by_cases hG : sharedFactor d (WithLp.toLp 2 ![z,0,0])=0
  · right
    rw [sharedFactor_at_origin hd0 hdU] at hG
    rw [sharedFactor_z_origin hd0 hdU]
    exact PinnedCriticalGeometry.simple_inflection hd0 hdU hG
  · exact Or.inl hG

end
end Resonance.PinnedCriticalFactor
