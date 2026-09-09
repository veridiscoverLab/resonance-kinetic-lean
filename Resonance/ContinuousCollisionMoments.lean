import Resonance.PhaseEnergy
import Resonance.PhysicalBalance
import Resonance.JetCollisionBounds
import Resonance.JetEnergy

/-! The original continuous sharp-cube collision map has all five moments
zero. The proof uses the same disintegrated four-leg measure and full cubic;
no independent conservation hypothesis is placed on a tensor equation. -/
open Set MeasureTheory
open scoped ENNReal
namespace Resonance.ContinuousCollisionMoments
noncomputable section
open FreeTransport ResonantMeasure FiberContinuity CollisionFiber PhaseEnergy WeightedPhysicalForm

abbrev CubeFunction (R : ℝ) := C(MomentumDomain R,ℝ)

def momentTest (R : ℝ) (θ : Thermodynamics.Parameter) : CubeFunction R :=
  ⟨fun k => reciprocalProfile θ k,(reciprocalProfile_continuous θ).comp continuous_subtype_val⟩

theorem cube_continuous_integrable (R : ℝ) (f : CubeFunction R) :
    Integrable f (momentumMeasure R) :=
  f.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace f)

def cubeIntegralLinear (R : ℝ) : CubeFunction R →ₗ[ℝ] ℝ where
  toFun f := ∫ k, f k ∂momentumMeasure R
  map_add' f g := integral_add (cube_continuous_integrable R f) (cube_continuous_integrable R g)
  map_smul' c f := integral_smul c f

def cubeIntegral (R : ℝ) : CubeFunction R →L[ℝ] ℝ :=
  (cubeIntegralLinear R).mkContinuous (momentumMeasure R univ).toReal (fun f => by
    change ‖∫ k, f k ∂momentumMeasure R‖ ≤ (momentumMeasure R univ).toReal*‖f‖
    simpa only [Measure.real,mul_comm] using norm_integral_le_of_norm_le_const
      (μ := momentumMeasure R) (C := ‖f‖) (Filter.Eventually.of_forall f.norm_coe_le_norm))

def moment (R : ℝ) (θ : Thermodynamics.Parameter) : CubeFunction R →L[ℝ] ℝ :=
  (cubeIntegral R).comp (ContinuousLinearMap.mul ℝ (CubeFunction R) (momentTest R θ))

theorem moment_integral (R : ℝ) (θ : Thermodynamics.Parameter) (f : CubeFunction R) :
    moment R θ f = ∫ k, reciprocalProfile θ k*f k ∂momentumMeasure R := rfl

theorem extension_memLp (R : ℝ) (f : CubeFunction R) :
    MemLp (continuousExtension R f) ∞ (PhysicalMarginal.physicalMeasure R) := by
  apply memLp_top_of_bound (continuousExtension R f).continuous.measurable.aestronglyMeasurable ‖f‖
  filter_upwards [ae_restrict_mem (measurable_cube R)] with k hk
  rw [continuousExtension_eq R f ⟨k,hk⟩]
  exact f.norm_coe_le_norm ⟨k,hk⟩

/-- The actual collisionMap on C(D) and every quadratic collision invariant.
θ is unrestricted, so all five independent coefficients are included. -/
theorem collision_five_moments {R : ℝ} (hR : 0 ≤ R)
    (f : CubeFunction R) (θ : Thermodynamics.Parameter) :
    moment R θ (collisionMap R hR f)=0 := by
  let fe := continuousExtension R f
  have hf : ∀ k∈cube R,‖fe k‖≤‖f‖ := by
    intro k hk
    change ‖continuousExtension R f k‖≤‖f‖
    rw [continuousExtension_eq R f ⟨k,hk⟩]
    exact f.norm_coe_le_norm ⟨k,hk⟩
  have hφ : ∀ k∈cube R,‖reciprocalProfile θ k‖≤‖momentTest R θ‖ :=
    fun k hk => (momentTest R θ).norm_coe_le_norm ⟨k,hk⟩
  have hw := collisionOutput_weak_pairing hR (norm_nonneg f) (norm_nonneg (momentTest R θ))
    fe (reciprocalProfile θ) fe.continuous.measurable (reciprocalProfile_continuous θ).measurable hf hφ
  have hc := PhysicalBalance.original_five_conservation hR fe (extension_memLp R f) θ
  have hz : (∫ k : E,reciprocalProfile θ k*collisionOutput R fe k)=0 := by
    rw [hw]
    simpa only [WeakCollision.originalDensity,collisionIntegrand,mul_comm] using hc
  have hind : (cube R).indicator (fun k => reciprocalProfile θ k*collisionOutput R fe k) =
      fun k => reciprocalProfile θ k*collisionOutput R fe k := by
    funext k
    by_cases hk : k∈cube R
    · exact indicator_of_mem hk _
    · simp only [indicator_of_notMem hk,collisionOutput_zero_outside R fe hk,mul_zero]
  have hr : (∫ k in cube R,reciprocalProfile θ k*collisionOutput R fe k)=0 := by
    rw [←integral_indicator (measurable_cube R),hind,hz]
  have hm : MeasurePreserving ((↑) : MomentumDomain R → E)
      (momentumMeasure R) (volume.restrict (cube R)) :=
    ⟨measurable_subtype_coe,momentumMeasure_map R⟩
  rw [moment_integral]
  calc
    (∫ k : MomentumDomain R,reciprocalProfile θ k*collisionMap R hR f k ∂momentumMeasure R) =
        ∫ k : MomentumDomain R,reciprocalProfile θ k*collisionOutput R fe k ∂momentumMeasure R := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun k => congrArg (fun x => reciprocalProfile θ k*x)
        (collisionMap_apply R hR f fe (continuousExtension_eq R f) k)
    _ = ∫ k in cube R,reciprocalProfile θ k*collisionOutput R fe k :=
      hm.integral_comp (MeasurableEmbedding.subtype_coe (measurable_cube R))
        (fun k : E => reciprocalProfile θ k*collisionOutput R fe k)
    _ = 0 := hr

def spatialMomentLinear (R : ℝ) (θ : Thermodynamics.Parameter) :
    Distribution R →ₗ[ℝ] C(SpatialTorus,ℝ) where
  toFun f := ⟨fun X => moment R θ (f.curry X),(moment R θ).continuous.comp f.curry.continuous⟩
  map_add' f g := by
    ext X
    change moment R θ ((f+g).curry X)=moment R θ (f.curry X)+moment R θ (g.curry X)
    have h : (f+g).curry X=f.curry X+g.curry X := by ext k; rfl
    rw [h,map_add]
  map_smul' c f := by
    ext X
    change moment R θ ((c • f).curry X)=c • moment R θ (f.curry X)
    have h : (c • f).curry X=c • f.curry X := by ext k; rfl
    rw [h,map_smul]

theorem spatialMomentLinear_bound (R : ℝ) (θ : Thermodynamics.Parameter) (f : Distribution R) :
    ‖spatialMomentLinear R θ f‖ ≤ ‖moment R θ‖*‖f‖ := by
  apply (ContinuousMap.norm_le _ (mul_nonneg (norm_nonneg _) (norm_nonneg f))).mpr
  intro X
  exact ((moment R θ).le_opNorm (f.curry X)).trans
    (mul_le_mul_of_nonneg_left (SpatialCollision.momentumSection_norm_le f X) (norm_nonneg _))

def spatialMoment (R : ℝ) (θ : Thermodynamics.Parameter) :
    Distribution R →L[ℝ] C(SpatialTorus,ℝ) :=
  (spatialMomentLinear R θ).mkContinuous ‖moment R θ‖ (spatialMomentLinear_bound R θ)

theorem spatialMoment_apply (R : ℝ) (θ : Thermodynamics.Parameter) (f : Distribution R)
    (X : SpatialTorus) :
    spatialMoment R θ f X = ∫ k,reciprocalProfile θ k*f (X,k) ∂momentumMeasure R := rfl

theorem spatial_collision_five_moments {R : ℝ} (hR : 0 ≤ R)
    (f : Distribution R) (θ : Thermodynamics.Parameter) :
    spatialMoment R θ (SpatialCollision.collision R hR f)=0 := by
  ext X
  exact collision_five_moments hR (f.curry X) θ

/-- Differentiation is performed on the common translation orbit of the
same full collision output. All original spatial locations are retained. -/
theorem spatial_derivative_collision_five_moments {R : ℝ} (hR : 0 ≤ R)
    (p : JetCollision.Space R) (θ : Thermodynamics.Parameter)
    (n : ℕ) (hn : n ≤ 3) (v : Fin n → SpatialChainRule.RealPosition) :
    spatialMoment R θ (JetEnergy.spatialDerivative R n hn v (JetCollision.collision R hR p))=0 := by
  have he : (spatialMoment R θ) ∘
      SpatialTranslationOrbit.distributionOrbit (JetCollision.readback (JetCollision.collision R hR p)) =
      fun _ : SpatialChainRule.RealPosition => (0 : C(SpatialTorus,ℝ)) := by
    funext x
    change spatialMoment R θ
      (SpatialTranslationOrbit.distributionOrbit (JetCollision.readback (JetCollision.collision R hR p)) x)=0
    rw [JetCollisionBounds.orbit_collision hR p]
    exact spatial_collision_five_moments hR _ θ
  have hd := (spatialMoment R θ).iteratedFDeriv_comp_left
    (f := SpatialTranslationOrbit.distributionOrbit
      (JetCollision.readback (JetCollision.collision R hR p)))
    (x := (0 : SpatialChainRule.RealPosition)) (i := n)
    (SpatialTranslationOrbit.distributionOrbit_contDiff (JetCollision.collision R hR p)).contDiffAt
    (by exact_mod_cast hn)
  rw [he] at hd
  have h := congrArg (fun A => A v) hd
  change spatialMoment R θ
    (iteratedFDeriv ℝ n (SpatialTranslationOrbit.distributionOrbit
      (JetCollision.readback (JetCollision.collision R hR p))) 0 v)=0
  simpa using h.symm

def parameterWeight (R : ℝ) (a : C(SpatialTorus,Thermodynamics.Parameter)) : Distribution R :=
  ⟨fun z => reciprocalProfile (a z.1) z.2, by
    unfold reciprocalProfile Entropy.denominator
    apply continuous_finset_sum
    intro i _
    apply Continuous.mul
    · exact (continuous_apply i).comp (a.continuous.comp continuous_fst)
    · exact (Entropy.fiveInvariants_continuous i).comp
        (WeightedJointMeasure.coordinates_continuous.comp (continuous_subtype_val.comp continuous_snd))⟩

/-- Macroscopic coefficients may vary over the same original spatial torus.
The zero-moment identity is first pointwise in X, then integrated with the
actual phase measure. -/
theorem phase_derivative_collision_moment_zero {R : ℝ} (hR : 0 ≤ R)
    (p : JetCollision.Space R) (a : C(SpatialTorus,Thermodynamics.Parameter))
    (n : ℕ) (hn : n ≤ 3) (v : Fin n → SpatialChainRule.RealPosition) :
    integralCLM R (parameterWeight R a *
      JetEnergy.spatialDerivative R n hn v (JetCollision.collision R hR p))=0 := by
  let f := JetEnergy.spatialDerivative R n hn v (JetCollision.collision R hR p)
  change (∫ z, (parameterWeight R a*f) z
    ∂((volume : Measure SpatialTorus).prod (momentumMeasure R)))=0
  rw [integral_prod _ (PhaseEnergy.continuous_integrable R (parameterWeight R a*f))]
  apply integral_eq_zero_of_ae
  apply Filter.Eventually.of_forall
  intro X
  have h := congrArg (fun F : C(SpatialTorus,ℝ) => F X)
    (spatial_derivative_collision_five_moments hR p (a X) n hn v)
  exact h

/-- The manuscript's macroscopic N Ψ component is orthogonal to the
normalized full collision derivative. Both factors contain the same N. -/
theorem normalized_macro_collision_pairing_zero {R : ℝ} (hR : 0 ≤ R)
    (p : JetCollision.Space R) (a : C(SpatialTorus,Thermodynamics.Parameter))
    (N : Distribution R) (hN : ∀ z,N z≠0)
    (n : ℕ) (hn : n ≤ 3) (v : Fin n → SpatialChainRule.RealPosition) :
    (∫ z, (N z*parameterWeight R a z)*
      (JetEnergy.spatialDerivative R n hn v (JetCollision.collision R hR p) z/N z)
      ∂phaseMeasure R)=0 := by
  have he : (fun z => (N z*parameterWeight R a z)*
      (JetEnergy.spatialDerivative R n hn v (JetCollision.collision R hR p) z/N z)) =
      fun z => parameterWeight R a z*
        JetEnergy.spatialDerivative R n hn v (JetCollision.collision R hR p) z := by
    funext z
    field_simp [hN z]
  rw [he]
  exact phase_derivative_collision_moment_zero hR p a n hn v

theorem normalized_collision_source_continuous (R : ℝ) (hR : 0 ≤ R)
    (p : JetCollision.Space R) (N : Distribution R) (hN : ∀ z,N z≠0)
    (n : ℕ) (hn : n ≤ 3) (v : Fin n → SpatialChainRule.RealPosition) :
    Continuous (fun z => JetEnergy.spatialDerivative R n hn v
      (JetCollision.collision R hR p) z/N z) :=
  (JetEnergy.spatialDerivative R n hn v (JetCollision.collision R hR p)).continuous.div N.continuous hN

/-- The precise coframe test replacement used in the physical relative
energy: subtraction of the entire N Ψ macro component does not change the
pairing with any actual spatial derivative of the full collision output. -/
theorem coframe_collision_test_replacement {R : ℝ} (hR : 0 ≤ R)
    (p : JetCollision.Space R) (a : C(SpatialTorus,Thermodynamics.Parameter))
    (N η : Distribution R) (hN : ∀ z,N z≠0)
    (n : ℕ) (hn : n ≤ 3) (v : Fin n → SpatialChainRule.RealPosition) :
    (∫ z, (η z-N z*parameterWeight R a z)*
      (JetEnergy.spatialDerivative R n hn v (JetCollision.collision R hR p) z/N z)
      ∂phaseMeasure R) =
    ∫ z, η z*(JetEnergy.spatialDerivative R n hn v (JetCollision.collision R hR p) z/N z)
      ∂phaseMeasure R := by
  let S : Distribution R := ⟨fun z => JetEnergy.spatialDerivative R n hn v
    (JetCollision.collision R hR p) z/N z,normalized_collision_source_continuous R hR p N hN n hn v⟩
  have hi := PhaseEnergy.continuous_integrable R (η*S)
  have hj := PhaseEnergy.continuous_integrable R ((N*parameterWeight R a)*S)
  simp_rw [sub_mul]
  change (∫ z, (η*S) z-((N*parameterWeight R a)*S) z ∂phaseMeasure R)=
    ∫ z, (η*S) z ∂phaseMeasure R
  rw [integral_sub hi hj]
  have hz : (∫ z, ((N*parameterWeight R a)*S) z ∂phaseMeasure R)=0 :=
    normalized_macro_collision_pairing_zero hR p a N hN n hn v
  rw [hz,sub_zero]

end
end Resonance.ContinuousCollisionMoments

#check Resonance.ContinuousCollisionMoments.cube_continuous_integrable
#print axioms Resonance.ContinuousCollisionMoments.cube_continuous_integrable
#check Resonance.ContinuousCollisionMoments.moment_integral
#print axioms Resonance.ContinuousCollisionMoments.moment_integral
#check Resonance.ContinuousCollisionMoments.extension_memLp
#print axioms Resonance.ContinuousCollisionMoments.extension_memLp
#check Resonance.ContinuousCollisionMoments.collision_five_moments
#print axioms Resonance.ContinuousCollisionMoments.collision_five_moments
#check Resonance.ContinuousCollisionMoments.spatialMomentLinear_bound
#print axioms Resonance.ContinuousCollisionMoments.spatialMomentLinear_bound
#check Resonance.ContinuousCollisionMoments.spatialMoment_apply
#print axioms Resonance.ContinuousCollisionMoments.spatialMoment_apply
#check Resonance.ContinuousCollisionMoments.spatial_collision_five_moments
#print axioms Resonance.ContinuousCollisionMoments.spatial_collision_five_moments
#check Resonance.ContinuousCollisionMoments.spatial_derivative_collision_five_moments
#print axioms Resonance.ContinuousCollisionMoments.spatial_derivative_collision_five_moments
#check Resonance.ContinuousCollisionMoments.phase_derivative_collision_moment_zero
#print axioms Resonance.ContinuousCollisionMoments.phase_derivative_collision_moment_zero
#check Resonance.ContinuousCollisionMoments.normalized_macro_collision_pairing_zero
#print axioms Resonance.ContinuousCollisionMoments.normalized_macro_collision_pairing_zero
#check Resonance.ContinuousCollisionMoments.normalized_collision_source_continuous
#print axioms Resonance.ContinuousCollisionMoments.normalized_collision_source_continuous
#check Resonance.ContinuousCollisionMoments.coframe_collision_test_replacement
#print axioms Resonance.ContinuousCollisionMoments.coframe_collision_test_replacement

#check Resonance.ContinuousCollisionMoments.cube_continuous_integrable
#print axioms Resonance.ContinuousCollisionMoments.cube_continuous_integrable
#check Resonance.ContinuousCollisionMoments.moment_integral
#print axioms Resonance.ContinuousCollisionMoments.moment_integral
#check Resonance.ContinuousCollisionMoments.extension_memLp
#print axioms Resonance.ContinuousCollisionMoments.extension_memLp
#check Resonance.ContinuousCollisionMoments.collision_five_moments
#print axioms Resonance.ContinuousCollisionMoments.collision_five_moments
#check Resonance.ContinuousCollisionMoments.spatialMomentLinear_bound
#print axioms Resonance.ContinuousCollisionMoments.spatialMomentLinear_bound
#check Resonance.ContinuousCollisionMoments.spatialMoment_apply
#print axioms Resonance.ContinuousCollisionMoments.spatialMoment_apply
#check Resonance.ContinuousCollisionMoments.spatial_collision_five_moments
#print axioms Resonance.ContinuousCollisionMoments.spatial_collision_five_moments
#check Resonance.ContinuousCollisionMoments.spatial_derivative_collision_five_moments
#print axioms Resonance.ContinuousCollisionMoments.spatial_derivative_collision_five_moments
#check Resonance.ContinuousCollisionMoments.phase_derivative_collision_moment_zero
#print axioms Resonance.ContinuousCollisionMoments.phase_derivative_collision_moment_zero
#check Resonance.ContinuousCollisionMoments.normalized_macro_collision_pairing_zero
#print axioms Resonance.ContinuousCollisionMoments.normalized_macro_collision_pairing_zero
#check Resonance.ContinuousCollisionMoments.normalized_collision_source_continuous
#print axioms Resonance.ContinuousCollisionMoments.normalized_collision_source_continuous
#check Resonance.ContinuousCollisionMoments.coframe_collision_test_replacement
#print axioms Resonance.ContinuousCollisionMoments.coframe_collision_test_replacement
