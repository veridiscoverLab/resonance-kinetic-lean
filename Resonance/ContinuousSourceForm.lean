import Resonance.ContinuousSourceCoordinates
import Resonance.ContinuousCollisionForm
import Resonance.CubeContinuousEssentialNorm

/-! The actual continuous normalized derivative and the fixed H_nu form
are identified through all four original marginal maps. -/
open Set MeasureTheory
open scoped ENNReal
namespace Resonance.ContinuousSourceForm
noncomputable section
set_option maxHeartbeats 2000000
open ResonantMeasure Thermodynamics WeightedJointMeasure
open ContinuousSourceCoordinates CubeLinftyCoordinates ActualPairNormalization
open ProfileBanachSmooth PhysicalWeightedCoercivity

theorem sourceMap_extension_ae {R : ℝ} (hR : 0<R) (f : C(cube R,ℝ)) :
    (sourceMap hR f : E→ℝ)=ᵐ[cubeVolume R] FiberContinuity.continuousExtension R f := by
  filter_upwards [sourceMap_ae hR f,ae_restrict_mem (measurable_cube R)] with k hf hk
  rw [hf,zeroExtension_apply R f ⟨k,hk⟩,FiberContinuity.continuousExtension_eq R f ⟨k,hk⟩]

theorem sourceMap_leg_ae {R : ℝ} (hR : 0<R) {θ : Parameter}
    (hθ : θ∈positiveDomain R) (f : C(cube R,ℝ)) (i : Fin 4) :
    (fun q : FourMomenta=>sourceMap hR f (q i))=ᵐ[jointMeasure R θ]
      (fun q=>FiberContinuity.continuousExtension R f (q i)) :=
  (FrequencyWeightedForm.all_legs_preserve R θ i).quasiMeasurePreserving.ae_eq
    ((cube_marginal_equivalent hR hθ).2.ae_eq (sourceMap_extension_ae hR f))

theorem sourceMap_difference_ae {R : ℝ} (hR : 0<R) {θ : Parameter}
    (hθ : θ∈positiveDomain R) (f : C(cube R,ℝ)) :
    CollisionForm.rawDifference (fun k=>sourceMap hR f k/profile θ k)=ᵐ[jointMeasure R θ]
      WeightedPhysicalForm.weightedDifference θ (FiberContinuity.continuousExtension R f) := by
  filter_upwards [sourceMap_leg_ae hR hθ f 0,sourceMap_leg_ae hR hθ f 1,
    sourceMap_leg_ae hR hθ f 2,sourceMap_leg_ae hR hθ f 3] with q h0 h1 h2 h3
  simp only [CollisionForm.rawDifference,WeightedPhysicalForm.weightedDifference,
    PhysicalMarginal.completeDifference,h0,h1,h2,h3]

theorem sourceMap_form {R : ℝ} (hR : 0<R) {θ : Parameter}
    (hθ : θ∈positiveDomain R) (u v : C(cube R,ℝ)) :
    physicalForm hR.le hθ (sourceMap hR u) (sourceMap hR v)=
      WeightedPhysicalForm.form R θ (FiberContinuity.continuousExtension R u)
        (FiberContinuity.continuousExtension R v) := by
  rw [physical_form_integral]
  apply integral_congr_ae
  filter_upwards [sourceMap_difference_ae hR hθ u,sourceMap_difference_ae hR hθ v] with q hu hv
  rw [hu,hv]

theorem normalized_derivative_pairing {R : ℝ} (hR : 0<R) {θ : Parameter}
    (hθ : θ∈positiveDomain R) (u v : C(cube R,ℝ)) :
    ContinuousCollisionMoments.cubeIntegral R
      (v*(denominatorMap R θ*fderiv ℝ (FiberContinuity.collisionMap R hR.le)
        (profileMap R θ) (profileMap R θ*u)))=
      -physicalForm hR.le hθ (sourceMap hR u) (sourceMap hR v) := by
  rw [sourceMap_form]
  have hN : profileMap R θ=ContinuousCollisionForm.rjCube hθ := by
    ext k
    exact profileMap_apply hθ k
  have hD : denominatorMap R θ=ContinuousCollisionForm.inverseCube
      (ContinuousCollisionForm.rjCube hθ) (fun k=>(ContinuousCollisionForm.rjCube_pos hθ k).ne') := by
    ext k
    change denominatorMap R θ k=(profile θ k)⁻¹
    rw [denominatorMap_apply,profile_eq_inverse_denominator,inv_inv]
  rw [hN,hD,←mul_assoc]
  exact ContinuousCollisionForm.rj_fderiv_full_form hR.le hθ u v

theorem sourceMap_cube_pairing {R : ℝ} (hR : 0<R) (u v : C(cube R,ℝ)) :
    (∫k,sourceMap hR u k*zeroExtension R v k∂cubeVolume R)=
      ContinuousCollisionMoments.cubeIntegral R (u*v) := by
  have hm : MeasurePreserving ((↑) : FreeTransport.MomentumDomain R→E)
      (PhaseEnergy.momentumMeasure R) (cubeVolume R) :=
    ⟨measurable_subtype_coe,PhaseEnergy.momentumMeasure_map R⟩
  calc
    _=∫k,zeroExtension R u k*zeroExtension R v k∂cubeVolume R := by
      apply integral_congr_ae
      filter_upwards [sourceMap_ae hR u] with k hk
      rw [hk]
    _=∫k : FreeTransport.MomentumDomain R,zeroExtension R u k*zeroExtension R v k∂PhaseEnergy.momentumMeasure R :=
      (hm.integral_comp (MeasurableEmbedding.subtype_coe (measurable_cube R)) _).symm
    _=_ := by
      apply integral_congr_ae
      exact ae_of_all _ (fun k=>by
        change zeroExtension R u k*zeroExtension R v k=(u*v) k
        rw [zeroExtension_apply,zeroExtension_apply]
        rfl)

theorem sourceMap_bounded {R : ℝ} (hR : 0<R) (f : C(cube R,ℝ)) :
    MemLp (sourceMap hR f : E→ℝ) ∞ (ReferenceFrequencySpace.referenceMeasure R) := by
  apply memLp_top_of_bound (Lp.stronglyMeasurable (sourceMap hR f)).aestronglyMeasurable ‖f‖
  filter_upwards [sourceMap_reference_ae hR f,
    (ReferenceFrequencySpace.reference_volume_equivalent hR).2.ae_le (zeroExtension_bound R f)] with k he hb
  rwa [he]

theorem sourceMap_injective {R : ℝ} (hR : 0<R) : Function.Injective (sourceMap hR) := by
  intro f g he
  apply CubeContinuousEssentialNorm.continuous_ae_eq hR f g
  have hf := sourceMap_ae hR f
  rw [he] at hf
  exact hf.symm.trans (sourceMap_ae hR g)

theorem cube_square_zero {R : ℝ} (hR : 0<R) (f : C(cube R,ℝ))
    (hz : ContinuousCollisionMoments.cubeIntegral R (f*f)=0) : f=0 := by
  have hi : (∫k,(sourceMap hR f k)^2∂cubeVolume R)=0 := by
    rw [←sourceMap_cube_pairing hR f f] at hz
    refine (integral_congr_ae ?_).trans hz
    filter_upwards [sourceMap_ae hR f] with k hk
    rw [hk,pow_two]
  have he := BoundedResolventUniqueness.square_zero_imp_zero hR (sourceMap hR f)
    (sourceMap_bounded hR f) hi
  apply sourceMap_injective hR
  rwa [map_zero]

theorem cube_tests_separate {R : ℝ} (hR : 0<R) (f : C(cube R,ℝ))
    (hz : ∀v : C(cube R,ℝ),ContinuousCollisionMoments.cubeIntegral R (v*f)=0) : f=0 :=
  cube_square_zero hR f (hz f)

end
end Resonance.ContinuousSourceForm
