import Resonance.JetMomentDynamics
import Resonance.ThermodynamicJets
import Resonance.CoareaNormalization

/-! Actual matching on the full positive moment chart. The kinetic moments
are computed from the same original cube and mild solution. Their dynamics
are derived from JetMomentDynamics, not supplied as a macroscopic hypothesis. -/
open Set MeasureTheory
open scoped BigOperators
namespace Resonance.ActualMatchedMoments
noncomputable section
open FreeTransport JetCollision SpatialChainRule SpatialJetSpace
open ContinuousCollisionMoments JetMomentDynamics Thermodynamics ThermodynamicChart
open WeightedPhysicalForm WeightedJointMeasure PhaseEnergy
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 30000

def basisParameter (i : Fin 5) : Parameter := Pi.single i 1

theorem basis_reciprocal (i : Fin 5) (k : ResonantMeasure.E) :
    reciprocalProfile (basisParameter i) k=Entropy.fiveInvariants i (coordinates k) := by
  simp [reciprocalProfile,basisParameter,Entropy.denominator,Pi.single_apply]

def moments (R : ℝ) : CubeFunction R →L[ℝ] Parameter :=
  ContinuousLinearMap.pi (fun i => moment R (basisParameter i))

theorem moments_integral (R : ℝ) (f : CubeFunction R) (i : Fin 5) :
    moments R f i = ∫ k,Entropy.fiveInvariants i (coordinates k)*f k ∂momentumMeasure R := by
  change moment R (basisParameter i) f=_
  rw [moment_integral]
  simp_rw [basis_reciprocal]

def actualMoments (R : ℝ) (f : Distribution R) : C(SpatialTorus,Parameter) :=
  ⟨fun X => moments R (f.curry X),(moments R).continuous.comp f.curry.continuous⟩

theorem actualMoments_component (R : ℝ) (f : Distribution R) (X : SpatialTorus) (i : Fin 5) :
    actualMoments R f X i=spatialMoment R (basisParameter i) f X := rfl

def rjCube (R : ℝ) (θ : Parameter) (hθ : θ∈positiveDomain R) : CubeFunction R :=
  ⟨fun k => profile θ k, by
    apply Continuous.inv₀ ((reciprocalProfile_continuous θ).comp continuous_subtype_val)
    intro k
    exact ne_of_gt (hθ (coordinates k) ((coordinates_cube R k).mp k.property))⟩

theorem rjCube_pos (R : ℝ) (θ : Parameter) (hθ : θ∈positiveDomain R)
    (k : MomentumDomain R) : 0<rjCube R θ hθ k := profile_pos hθ k.property

/-- This identifies the exact Euclidean cube moments with the original
thermodynamic Pi-Lebesgue moment map; no volume normalization is suppressed. -/
theorem rjCube_moments (R : ℝ) (θ : Parameter) (hθ : θ∈positiveDomain R) :
    moments R (rjCube R θ hθ)=momentMap R θ := by
  ext i
  rw [moments_integral]
  have hm : MeasurePreserving ((↑) : MomentumDomain R → ResonantMeasure.E)
      (momentumMeasure R) (volume.restrict (ResonantMeasure.cube R)) :=
    ⟨measurable_subtype_coe,momentumMeasure_map R⟩
  calc
    (∫ k : MomentumDomain R,Entropy.fiveInvariants i (coordinates k)*rjCube R θ hθ k
        ∂momentumMeasure R) =
        ∫ k in ResonantMeasure.cube R,Entropy.fiveInvariants i (coordinates k)*profile θ k :=
      hm.integral_comp (MeasurableEmbedding.subtype_coe (ResonantMeasure.measurable_cube R))
        (fun k : ResonantMeasure.E => Entropy.fiveInvariants i (coordinates k)*profile θ k)
    _ = momentMap R θ i := by
      have hF : AEStronglyMeasurable
          (fun k : ResonantMeasure.E => Entropy.fiveInvariants i (coordinates k)*profile θ k)
          (volume.restrict (ResonantMeasure.cube R)) :=
        (((Entropy.fiveInvariants_continuous i).comp coordinates_continuous).measurable.mul
          (profile_measurable θ)).aestronglyMeasurable
      exact CoareaNormalization.thermodynamic_cube_integral R _ hF

def matchedValue (R : ℝ) (hR : 0<R) (f : Distribution R) (X : SpatialTorus) : Parameter :=
  momentInverse R hR (actualMoments R f X)

theorem matched_positive (R : ℝ) (hR : 0<R) (f : Distribution R) (X : SpatialTorus)
    (hX : actualMoments R f X∈momentImage R) : matchedValue R hR f X∈positiveDomain R :=
  momentInverse_mem R hR _ hX

theorem matched_unique (R : ℝ) (hR : 0<R) (f : Distribution R) (X : SpatialTorus)
    (hX : actualMoments R f X∈momentImage R) :
    ∃! θ : Parameter,θ∈positiveDomain R ∧ momentMap R θ=actualMoments R f X :=
  existsUnique_matched_parameter R hR _ hX

def matchedField (R : ℝ) (hR : 0<R) (f : Distribution R)
    (hf : ∀ X,actualMoments R f X∈momentImage R) : C(SpatialTorus,Parameter) :=
  ⟨matchedValue R hR f,by
    apply continuous_iff_continuousAt.mpr
    intro X
    exact (momentInverse_contDiffAt R hR _ (hf X)).continuousAt.comp
      (actualMoments R f).continuous.continuousAt⟩

theorem matched_cube_moments (R : ℝ) (hR : 0<R) (f : Distribution R) (X : SpatialTorus)
    (hX : actualMoments R f X∈momentImage R) :
    moments R (rjCube R (matchedValue R hR f X) (matched_positive R hR f X hX))=
      actualMoments R f X := by
  rw [rjCube_moments]
  exact momentInverse_right R hR _ hX

theorem matched_micro_moments_zero (R : ℝ) (hR : 0<R) (f : Distribution R) (X : SpatialTorus)
    (hX : actualMoments R f X∈momentImage R) :
    moments R (f.curry X-rjCube R (matchedValue R hR f X)
      (matched_positive R hR f X hX))=0 := by
  rw [map_sub,matched_cube_moments R hR f X hX]
  exact sub_self _

theorem actualMoments_real_contDiff (R : ℝ) (p : Space R) :
    ContDiff ℝ 3 (fun x : RealPosition => actualMoments R (readback p) (torusQuotient x)) :=
  (moments R).contDiff.comp (toDistribution_contDiff p)

theorem matched_real_contDiffAt (R : ℝ) (hR : 0<R) (p : Space R) (x : RealPosition)
    (hx : actualMoments R (readback p) (torusQuotient x)∈momentImage R) :
    ContDiffAt ℝ 3 (fun y : RealPosition => matchedValue R hR (readback p) (torusQuotient y)) x :=
  (ThermodynamicJets.momentInverse_contDiffAt_finite R hR 3 _ hx).comp x
    (actualMoments_real_contDiff R p).contDiffAt

def divergenceVector (R : ℝ) (p : Space R) (x : RealPosition) : Parameter :=
  fun i => fluxDivergence R (basisParameter i) p x

theorem actual_moment_derivative {R T : ℝ} (hR : 0≤R) (hT : 0≤T)
    (c : ℝ) (p₀ : Space R) (p : ℝ→Space R) (hp : ContinuousOn p (Icc 0 T))
    (he : ∀ t∈Icc 0 T,readback (p t)=transport R t (readback p₀)+
      ∫ s in (0 : ℝ)..t,c • transport R (t-s)
        (SpatialCollision.collision R hR (readback (p s))))
    (x : RealPosition) {t : ℝ} (ht : t∈Icc 0 T) :
    HasDerivWithinAt (fun τ => actualMoments R (readback (p τ)) (torusQuotient x))
      (-divergenceVector R (p t) x) (Icc 0 T) t := by
  apply hasDerivWithinAt_pi.mpr
  intro i
  exact original_mild_local_five_balance hR hT c p₀ p hp he (basisParameter i) x ht

theorem actual_matched_time_derivative {R T : ℝ} (hR : 0<R) (hT : 0≤T)
    (c : ℝ) (p₀ : Space R) (p : ℝ→Space R) (hp : ContinuousOn p (Icc 0 T))
    (he : ∀ t∈Icc 0 T,readback (p t)=transport R t (readback p₀)+
      ∫ s in (0 : ℝ)..t,c • transport R (t-s)
        (SpatialCollision.collision R hR.le (readback (p s))))
    (x : RealPosition) {t : ℝ} (ht : t∈Icc 0 T)
    (hx : actualMoments R (readback (p t)) (torusQuotient x)∈momentImage R) :
    HasDerivWithinAt (fun τ => matchedValue R hR (readback (p τ)) (torusQuotient x))
      (fderiv ℝ (momentInverse R hR) (actualMoments R (readback (p t)) (torusQuotient x))
        (-divergenceVector R (p t) x)) (Icc 0 T) t := by
  exact (momentInverse_hasFDerivAt R hR _ hx).differentiableAt.hasFDerivAt.comp_hasDerivWithinAt t
    (actual_moment_derivative hR.le hT c p₀ p hp he x ht)

theorem actual_matched_gram_equation {R T : ℝ} (hR : 0<R) (hT : 0≤T)
    (c : ℝ) (p₀ : Space R) (p : ℝ→Space R) (hp : ContinuousOn p (Icc 0 T))
    (he : ∀ t∈Icc 0 T,readback (p t)=transport R t (readback p₀)+
      ∫ s in (0 : ℝ)..t,c • transport R (t-s)
        (SpatialCollision.collision R hR.le (readback (p s))))
    (x : RealPosition) {t : ℝ} (ht : t∈Icc 0 T)
    (hx : actualMoments R (readback (p t)) (torusQuotient x)∈momentImage R) :
    ∃ θt : Parameter,
      HasDerivWithinAt (fun τ => matchedValue R hR (readback (p τ)) (torusQuotient x))
        θt (Icc 0 T) t ∧
      (gramMatrix R (matchedValue R hR (readback (p t)) (torusQuotient x))).mulVec θt=
        divergenceVector R (p t) x := by
  refine ⟨_,actual_matched_time_derivative hR hT c p₀ p hp he x ht hx,?_⟩
  exact (momentInverse_fderiv_gram R hR _ hx (-divergenceVector R (p t) x)).trans
    (neg_neg _)

theorem actualMoments_real_hasFDerivAt (R : ℝ) (p : Space R) (x : RealPosition) :
    HasFDerivAt (fun y => actualMoments R (readback p) (torusQuotient y))
      ((moments R).comp (p.val.2.1 (torusQuotient x))) x :=
  (moments R).hasFDerivAt.comp x (p.property.1 x)

theorem matched_real_hasFDerivAt (R : ℝ) (hR : 0<R) (p : Space R) (x : RealPosition)
    (hx : actualMoments R (readback p) (torusQuotient x)∈momentImage R) :
    HasFDerivAt (fun y => matchedValue R hR (readback p) (torusQuotient y))
      ((fderiv ℝ (momentInverse R hR) (actualMoments R (readback p) (torusQuotient x))).comp
        ((moments R).comp (p.val.2.1 (torusQuotient x)))) x :=
  (momentInverse_hasFDerivAt R hR _ hx).differentiableAt.hasFDerivAt.comp x
    (actualMoments_real_hasFDerivAt R p x)

def matchedTimeRate (R : ℝ) (hR : 0<R) (p : Space R) (x : RealPosition) : Parameter :=
  fderiv ℝ (momentInverse R hR) (actualMoments R (readback p) (torusQuotient x))
    (-divergenceVector R p x)

def matchedSpatialDerivative (R : ℝ) (hR : 0<R) (p : Space R) (x : RealPosition) :
    RealPosition →L[ℝ] Parameter :=
  fderiv ℝ (fun y => matchedValue R hR (readback p) (torusQuotient y)) x

def matchedMaterialParameter (R : ℝ) (hR : 0<R) (p : Space R) (x : RealPosition)
    (k : MomentumDomain R) : Parameter :=
  matchedTimeRate R hR p x+matchedSpatialDerivative R hR p x
    (TransportMaterialDerivative.velocity R k)

theorem profile_parameter_hasFDerivAt (R : ℝ) (θ : Parameter) (hθ : θ∈positiveDomain R)
    (k : MomentumDomain R) :
    HasFDerivAt (fun β => profile β k)
      ((-(profile θ k)^2) • denominatorCLM (coordinates k)) θ := by
  have hd := (denominatorCLM (coordinates k)).hasFDerivAt (x := θ)
  have hn : denominatorCLM (coordinates k) θ≠0 := by
    rw [denominatorCLM_apply]
    exact ne_of_gt (hθ (coordinates k) ((coordinates_cube R k).mp k.property))
  have hi := (hasFDerivAt_inv hn).comp θ hd
  have he : (fun β => profile β k)=(fun x : ℝ => x⁻¹) ∘ denominatorCLM (coordinates k) := by
    funext β
    simp [profile,Entropy.rj,denominatorCLM_apply]
  rw [←he] at hi
  convert hi using 1
  ext b
  simp [profile,Entropy.rj,denominatorCLM_apply,inv_pow,mul_comm]

theorem logProfile_parameter_hasFDerivAt (R : ℝ) (θ : Parameter) (hθ : θ∈positiveDomain R)
    (k : MomentumDomain R) :
    HasFDerivAt (fun β => Real.log (profile β k))
      ((-profile θ k) • denominatorCLM (coordinates k)) θ := by
  have hn : profile θ k≠0 := ne_of_gt (profile_pos hθ k.property)
  have h := (profile_parameter_hasFDerivAt R θ hθ k).log hn
  convert h using 1
  ext b
  simp only [ContinuousLinearMap.smul_apply,smul_eq_mul]
  field_simp

/-- The coframe weight uses the actual matched parameter rate, read from the
actual moment equation. Its full material logarithmic derivative includes
the same momentum-dependent velocity; it is not a bounded-background premise. -/
theorem actual_matched_material_log_derivative {R T : ℝ} (hR : 0<R) (hT : 0≤T)
    (c : ℝ) (p₀ : Space R) (p : ℝ→Space R) (hp : ContinuousOn p (Icc 0 T))
    (he : ∀ t∈Icc 0 T,readback (p t)=transport R t (readback p₀)+
      ∫ s in (0 : ℝ)..t,c • transport R (t-s)
        (SpatialCollision.collision R hR.le (readback (p s))))
    (x : RealPosition) {t : ℝ} (ht : t∈Icc 0 T)
    (hx : actualMoments R (readback (p t)) (torusQuotient x)∈momentImage R)
    (k : MomentumDomain R) :
    ∃ Bt : ℝ,
      HasDerivWithinAt (fun τ => Real.log (profile
        (matchedValue R hR (readback (p τ)) (torusQuotient x)) k)) Bt (Icc 0 T) t ∧
      Bt+fderiv ℝ (fun y => Real.log (profile
          (matchedValue R hR (readback (p t)) (torusQuotient y)) k)) x
          (TransportMaterialDerivative.velocity R k)=
        -profile (matchedValue R hR (readback (p t)) (torusQuotient x)) k*
          reciprocalProfile (matchedMaterialParameter R hR (p t) x k) k := by
  let θ := matchedValue R hR (readback (p t)) (torusQuotient x)
  have hθ : θ∈positiveDomain R := matched_positive R hR _ _ hx
  have hl := logProfile_parameter_hasFDerivAt R θ hθ k
  have htime := hl.comp_hasDerivWithinAt t
    (actual_matched_time_derivative hR hT c p₀ p hp he x ht hx)
  have hxder := (matched_real_contDiffAt R hR (p t) x hx).differentiableAt (by norm_num)
  have hspace := hl.comp x hxder.hasFDerivAt
  simp only [Function.comp_def] at hspace
  refine ⟨_,htime,?_⟩
  rw [hspace.fderiv]
  change (-profile θ k)*denominatorCLM (coordinates k) (matchedTimeRate R hR (p t) x)+
    (-profile θ k)*denominatorCLM (coordinates k)
      (matchedSpatialDerivative R hR (p t) x (TransportMaterialDerivative.velocity R k))=_
  rw [←mul_add,←map_add,denominatorCLM_apply]
  rfl

#check basis_reciprocal
#check moments_integral
#check actualMoments_component
#check rjCube_pos
#check rjCube_moments
#check matched_positive
#check matched_unique
#check matched_cube_moments
#check matched_micro_moments_zero
#check actualMoments_real_contDiff
#check matched_real_contDiffAt
#check actual_moment_derivative
#check actual_matched_time_derivative
#check actual_matched_gram_equation
#check actualMoments_real_hasFDerivAt
#check matched_real_hasFDerivAt
#check profile_parameter_hasFDerivAt
#check logProfile_parameter_hasFDerivAt
#check actual_matched_material_log_derivative
#print axioms basis_reciprocal
#print axioms moments_integral
#print axioms actualMoments_component
#print axioms rjCube_pos
#print axioms rjCube_moments
#print axioms matched_positive
#print axioms matched_unique
#print axioms matched_cube_moments
#print axioms matched_micro_moments_zero
#print axioms actualMoments_real_contDiff
#print axioms matched_real_contDiffAt
#print axioms actual_moment_derivative
#print axioms actual_matched_time_derivative
#print axioms actual_matched_gram_equation
#print axioms actualMoments_real_hasFDerivAt
#print axioms matched_real_hasFDerivAt
#print axioms profile_parameter_hasFDerivAt
#print axioms logProfile_parameter_hasFDerivAt
#print axioms actual_matched_material_log_derivative

end
end Resonance.ActualMatchedMoments
