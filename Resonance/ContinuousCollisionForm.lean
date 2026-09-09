import Resonance.ContinuousCollisionMoments
import Resonance.ActualLinearization
import Resonance.FrequencyWeightedKernel

/-! The actual C(D) Fréchet derivative is read on the same full four-leg
measure. This connects the kinetic jet equation to the signed collision form;
no independently specified row derivative or dissipation premise is used. -/
open Set MeasureTheory
open scoped ENNReal
namespace Resonance.ContinuousCollisionForm
noncomputable section
open ResonantMeasure FreeTransport FiberContinuity CollisionFiber
open ContinuousCollisionMoments PhaseEnergy CollisionMultilinear WeakCollision
set_option maxHeartbeats 1200000

abbrev CubeFunction (R : ℝ) := C(MomentumDomain R,ℝ)

def restrictCube (R : ℝ) (f : C(E,ℝ)) : CubeFunction R :=
  ⟨fun k=>f k,f.continuous.comp continuous_subtype_val⟩

theorem restrictCube_extension (R : ℝ) (f : CubeFunction R) :
    restrictCube R (continuousExtension R f)=f := by
  ext k
  exact continuousExtension_eq R f k

theorem continuous_cube_memLp (R : ℝ) (f : C(E,ℝ)) :
    MemLp f ∞ (PhysicalMarginal.physicalMeasure R) := by
  apply memLp_top_of_bound f.continuous.measurable.aestronglyMeasurable ‖restrictCube R f‖
  filter_upwards [ae_restrict_mem (measurable_cube R)] with k hk
  exact (restrictCube R f).norm_coe_le_norm ⟨k,hk⟩

theorem collision_weak_pairing {R : ℝ} (hR : 0≤R) (f g : C(E,ℝ)) :
    cubeIntegral R (restrictCube R g*collisionMap R hR (restrictCube R f))=
      functional R f g := by
  have hf : ∀k∈cube R,‖f k‖≤‖restrictCube R f‖ :=
    fun k hk=>(restrictCube R f).norm_coe_le_norm ⟨k,hk⟩
  have hg : ∀k∈cube R,‖g k‖≤‖restrictCube R g‖ :=
    fun k hk=>(restrictCube R g).norm_coe_le_norm ⟨k,hk⟩
  have hw := collisionOutput_weak_pairing hR (norm_nonneg _) (norm_nonneg _)
    f g f.continuous.measurable g.continuous.measurable hf hg
  have hind : (cube R).indicator (fun k=>g k*collisionOutput R f k)=
      fun k=>g k*collisionOutput R f k := by
    funext k
    by_cases hk:k∈cube R
    · exact indicator_of_mem hk _
    · simp only [indicator_of_notMem hk,collisionOutput_zero_outside R f hk,mul_zero]
  have hm : MeasurePreserving ((↑):MomentumDomain R→E)
      (momentumMeasure R) (volume.restrict (cube R)) :=
    ⟨measurable_subtype_coe,momentumMeasure_map R⟩
  calc
    cubeIntegral R (restrictCube R g*collisionMap R hR (restrictCube R f))=
        ∫k:MomentumDomain R,g k*collisionOutput R f k∂momentumMeasure R := by
      apply integral_congr_ae
      apply ae_of_all
      intro k
      change g k*collisionMap R hR (restrictCube R f) k=_
      rw [collisionMap_apply R hR _ f (fun _=>rfl)]
    _=∫k in cube R,g k*collisionOutput R f k :=
      hm.integral_comp (MeasurableEmbedding.subtype_coe (measurable_cube R))
        (fun k:E=>g k*collisionOutput R f k)
    _=∫k:E,g k*collisionOutput R f k := by
      rw [←integral_indicator (measurable_cube R),hind]
    _=functional R f g := by
      rw [hw,functional_eq_original hR (continuous_cube_memLp R f) (continuous_cube_memLp R g)]
      apply integral_congr_ae
      exact ae_of_all _ fun _=>mul_comm _ _

theorem collision_fderiv_full_pairing {R : ℝ} (hR : 0≤R)
    (f h g : CubeFunction R) :
    cubeIntegral R (g*fderiv ℝ (collisionMap R hR) f h)=
      ∫q,linearDensity (continuousExtension R f) (continuousExtension R h)
        (continuousExtension R g) q∂pairingMeasure R := by
  let F := continuousExtension R f
  let H := continuousExtension R h
  let G := continuousExtension R g
  let L : CubeFunction R→L[ℝ]ℝ :=
    (cubeIntegral R).comp (ContinuousLinearMap.mul ℝ (CubeFunction R) g)
  have hp : HasDerivAt (fun t:ℝ=>f+t • h) h 0 := by
    simpa only [id_eq,one_smul] using ((hasDerivAt_id (0:ℝ)).smul_const h).const_add f
  have hc := (collisionMap_hasFDerivAt hR (f+(0:ℝ) • h)).comp_hasDerivAt 0 hp
  simp only [zero_smul,add_zero] at hc
  rw [←(collisionMap_hasFDerivAt hR f).fderiv] at hc
  have hl := L.hasFDerivAt.comp_hasDerivAt 0 hc
  have hr := functional_directional_derivative hR (extension_memLp R f)
    (extension_memLp R h) (extension_memLp R g)
  have heq : (fun t:ℝ=>L (collisionMap R hR (f+t • h)))=
      (fun t:ℝ=>functional R (fun k=>F k+t*H k) G) := by
    funext t
    have he : restrictCube R (F+t • H)=f+t • h := by
      ext k
      simp only [restrictCube,ContinuousMap.coe_mk,ContinuousMap.add_apply,
        ContinuousMap.smul_apply,smul_eq_mul,F,H,continuousExtension_eq]
    have hG : restrictCube R G=g := restrictCube_extension R g
    have hw := collision_weak_pairing hR (F+t • H) G
    rw [he,hG] at hw
    exact hw
  change HasDerivAt (fun t:ℝ=>L (collisionMap R hR (f+t • h)))
    (cubeIntegral R (g*fderiv ℝ (collisionMap R hR) f h)) 0 at hl
  rw [heq] at hl
  exact hl.unique hr

theorem collision_fderiv_original_row {R : ℝ} (hR : 0≤R)
    (f h g : CubeFunction R) :
    cubeIntegral R (g*fderiv ℝ (collisionMap R hR) f h)=
      ∫q,ActualLinearization.originalLinearDensity (continuousExtension R f)
        (continuousExtension R h) (continuousExtension R g) q∂pairingMeasure R := by
  letI := PhysicalBalance.physicalMeasure_finite hR
  rw [collision_fderiv_full_pairing]
  exact ActualLinearization.linear_full_eq_original hR (extension_memLp R f)
    (extension_memLp R h) ((extension_memLp R g).mono_exponent (by simp))

def inverseCube (N : CubeFunction R) (hN : ∀k,N k≠0) : CubeFunction R :=
  ⟨fun k=>(N k)⁻¹,N.continuous.inv₀ hN⟩

/-- The normalization uses the same N in the input direction and test.
All four derivative parents and all four test legs remain in the integral. -/
theorem normalized_fderiv_full_pairing {R : ℝ} (hR : 0≤R)
    (f N u v : CubeFunction R) (hN : ∀k,N k≠0) :
    cubeIntegral R ((v*inverseCube N hN)*fderiv ℝ (collisionMap R hR) f (N*u))=
      ∫q,(1/4:ℝ)*CollisionLinearization.linearCoefficient
        (fun i=>continuousExtension R f (q i))
        (fun i=>continuousExtension R N (q i)*continuousExtension R u (q i))*
        Collision.delta (fun i=>continuousExtension R v (q i)/continuousExtension R N (q i))
        ∂pairingMeasure R := by
  rw [collision_fderiv_full_pairing]
  apply integral_congr_ae
  filter_upwards [ae_iff.mpr (pairing_supported_on_fullResonance R)] with q hq
  have hdir : (fun i:Fin 4=>continuousExtension R (N*u) (q i))=
      (fun i=>continuousExtension R N (q i)*continuousExtension R u (q i)) := by
    funext i
    have hk:=hq.1 i
    rw [continuousExtension_eq R (N*u) ⟨q i,hk⟩,
      continuousExtension_eq R N ⟨q i,hk⟩,continuousExtension_eq R u ⟨q i,hk⟩]
    rfl
  have htest : (fun i:Fin 4=>continuousExtension R (v*inverseCube N hN) (q i))=
      (fun i=>continuousExtension R v (q i)/continuousExtension R N (q i)) := by
    funext i
    have hk:=hq.1 i
    rw [continuousExtension_eq R (v*inverseCube N hN) ⟨q i,hk⟩,
      continuousExtension_eq R v ⟨q i,hk⟩,continuousExtension_eq R N ⟨q i,hk⟩]
    rfl
  simp only [linearDensity,hdir,htest]

def rjCube {R : ℝ} {θ : Thermodynamics.Parameter}
    (hθ : θ∈Thermodynamics.positiveDomain R) : CubeFunction R :=
  ⟨fun k=>WeightedJointMeasure.profile θ k,
    continuousOn_iff_continuous_restrict.mp (FrequencyWeightedKernel.profile_continuousOn hθ)⟩

theorem rjCube_pos {R : ℝ} {θ : Thermodynamics.Parameter}
    (hθ : θ∈Thermodynamics.positiveDomain R) (k : MomentumDomain R) :
    0<rjCube hθ k := WeightedJointMeasure.profile_pos hθ k.property

theorem rj_fderiv_full_form {R : ℝ} (hR : 0≤R) {θ : Thermodynamics.Parameter}
    (hθ : θ∈Thermodynamics.positiveDomain R) (u v : CubeFunction R) :
    cubeIntegral R ((v*inverseCube (rjCube hθ) (fun k=>(rjCube_pos hθ k).ne'))*
      fderiv ℝ (collisionMap R hR) (rjCube hθ) (rjCube hθ*u))=
      -WeightedPhysicalForm.form R θ (continuousExtension R u) (continuousExtension R v) := by
  rw [normalized_fderiv_full_pairing,
    ←rj_linearized_form_identity hθ (continuousExtension R u) (continuousExtension R v)]
  apply integral_congr_ae
  filter_upwards [ae_iff.mpr (pairing_supported_on_fullResonance R)] with q hq
  have hN (i:Fin 4) : continuousExtension R (rjCube hθ) (q i)=
      WeightedJointMeasure.profile θ (q i) :=
    continuousExtension_eq R (rjCube hθ) ⟨q i,hq.1 i⟩
  simp only [hN,linearDensity]

theorem rj_fderiv_nonpositive {R : ℝ} (hR : 0≤R) {θ : Thermodynamics.Parameter}
    (hθ : θ∈Thermodynamics.positiveDomain R) (u : CubeFunction R) :
    cubeIntegral R ((u*inverseCube (rjCube hθ) (fun k=>(rjCube_pos hθ k).ne'))*
      fderiv ℝ (collisionMap R hR) (rjCube hθ) (rjCube hθ*u))≤0 := by
  rw [rj_fderiv_full_form]
  exact neg_nonpos.mpr (WeightedPhysicalForm.form_nonneg R θ _)

end
end Resonance.ContinuousCollisionForm

#check Resonance.ContinuousCollisionForm.restrictCube_extension
#check Resonance.ContinuousCollisionForm.continuous_cube_memLp
#check Resonance.ContinuousCollisionForm.collision_weak_pairing
#check Resonance.ContinuousCollisionForm.collision_fderiv_full_pairing
#check Resonance.ContinuousCollisionForm.collision_fderiv_original_row
#check Resonance.ContinuousCollisionForm.normalized_fderiv_full_pairing
#check Resonance.ContinuousCollisionForm.rjCube_pos
#check Resonance.ContinuousCollisionForm.rj_fderiv_full_form
#check Resonance.ContinuousCollisionForm.rj_fderiv_nonpositive
#print axioms Resonance.ContinuousCollisionForm.restrictCube_extension
#print axioms Resonance.ContinuousCollisionForm.continuous_cube_memLp
#print axioms Resonance.ContinuousCollisionForm.collision_weak_pairing
#print axioms Resonance.ContinuousCollisionForm.collision_fderiv_full_pairing
#print axioms Resonance.ContinuousCollisionForm.collision_fderiv_original_row
#print axioms Resonance.ContinuousCollisionForm.normalized_fderiv_full_pairing
#print axioms Resonance.ContinuousCollisionForm.rjCube_pos
#print axioms Resonance.ContinuousCollisionForm.rj_fderiv_full_form
#print axioms Resonance.ContinuousCollisionForm.rj_fderiv_nonpositive
