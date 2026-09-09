import Resonance.ContinuousCollisionForm
import Resonance.BoundedSourceMaps
import Resonance.CubeLinftyCoordinates
import Resonance.PhysicalMicroCoercivity

/-! The kinetic C(D) test is inserted in the actual fixed H_nu, with its
literal physical norm and full collision form. All representatives use the
same cube; the five-moment microcondition is an ordinary physical integral. -/
open Set MeasureTheory
open scoped ENNReal
namespace Resonance.ContinuousWeightedEnergy
noncomputable section
open ResonantMeasure FreeTransport FiberContinuity ContinuousCollisionForm
open ContinuousCollisionMoments PhaseEnergy ReferenceFrequencySpace
open PhysicalWeightedCoercivity PhysicalFiveBasis PhysicalMomentProjection
set_option maxHeartbeats 1500000

abbrev CubeFunction (R : ℝ) := C(MomentumDomain R,ℝ)

def toWeighted {R : ℝ} (hR : 0<R) : CubeFunction R→L[ℝ]ReferenceFrequencySpace.Space R :=
  (BoundedSourceMaps.sourceMap hR).comp (CubeLinftyCoordinates.embed R)

theorem toWeighted_ae {R : ℝ} (hR : 0<R) (f : CubeFunction R) :
    (toWeighted hR f:E→ℝ)=ᵐ[ActualPairNormalization.cubeVolume R] continuousExtension R f := by
  have hs:=BoundedSourceMaps.sourceVector_ae hR (CubeLinftyCoordinates.embed R f)
  filter_upwards [hs,CubeLinftyCoordinates.embed_ae R f,
    ae_restrict_mem (measurable_cube R)] with k hk he hcube
  change StrongBoundedCell.sourceVector hR (CubeLinftyCoordinates.embed R f) k=_
  rw [hk,he,CubeLinftyCoordinates.zeroExtension_apply R f ⟨k,hcube⟩,
    continuousExtension_eq R f ⟨k,hcube⟩]

theorem toWeighted_norm_square {R : ℝ} (hR : 0<R) (u : CubeFunction R) :
    ‖toWeighted hR u‖^2=
      ∫k:MomentumDomain R,CollisionFrequency.referenceFrequency R k*(u k)^2∂momentumMeasure R := by
  rw [←real_inner_self_eq_norm_sq,L2.inner_def]
  change (∫k,(toWeighted hR u k)*(toWeighted hR u k)∂
    (ActualPairNormalization.cubeVolume R).withDensity
      (fun k=>ENNReal.ofReal (CollisionFrequency.referenceFrequency R k)))=_
  rw [integral_withDensity_eq_integral_toReal_smul (reference_density_measurable R)
    (ae_of_all _ fun _=>ENNReal.ofReal_lt_top)]
  have he : (∫k,ENNReal.toReal (ENNReal.ofReal (CollisionFrequency.referenceFrequency R k)) •
      (toWeighted hR u k*toWeighted hR u k)∂ActualPairNormalization.cubeVolume R)=
      ∫k,CollisionFrequency.referenceFrequency R k*(continuousExtension R u k)^2
        ∂ActualPairNormalization.cubeVolume R := by
    apply integral_congr_ae
    filter_upwards [toWeighted_ae hR u,CornerInverseFrequency.referenceFrequency_positive_ae hR]
      with k hu hk
    rw [hu,ENNReal.toReal_ofReal hk.le]
    simp only [smul_eq_mul,pow_two]
  rw [he]
  have hm : MeasurePreserving ((↑):MomentumDomain R→E)
      (momentumMeasure R) (volume.restrict (cube R)) :=
    ⟨measurable_subtype_coe,momentumMeasure_map R⟩
  calc
    _=∫k:MomentumDomain R,CollisionFrequency.referenceFrequency R k*(continuousExtension R u k)^2
        ∂momentumMeasure R :=
      (hm.integral_comp (MeasurableEmbedding.subtype_coe (measurable_cube R))
        (fun k:E=>CollisionFrequency.referenceFrequency R k*(continuousExtension R u k)^2)).symm
    _=_ := by
      apply integral_congr_ae
      exact ae_of_all _ fun k=>by
        dsimp only
        rw [continuousExtension_eq R u k]

theorem toWeighted_form {R : ℝ} (hR : 0<R) {θ : Thermodynamics.Parameter}
    (hθ : θ∈Thermodynamics.positiveDomain R) (u v : CubeFunction R) :
    physicalForm hR.le hθ (toWeighted hR u) (toWeighted hR v)=
      WeightedPhysicalForm.form R θ (continuousExtension R u) (continuousExtension R v) := by
  rw [physical_form_integral]
  unfold WeightedPhysicalForm.form
  apply integral_congr_ae
  have hu := ae_all_iff.mpr (fun i:Fin 4=>
    (WeightedJointMeasure.leg_quasiMeasurePreserving_cube R θ i).ae_eq (toWeighted_ae hR u))
  have hv := ae_all_iff.mpr (fun i:Fin 4=>
    (WeightedJointMeasure.leg_quasiMeasurePreserving_cube R θ i).ae_eq (toWeighted_ae hR v))
  filter_upwards [hu,hv] with q hqu hqv
  simp only [Function.comp_def] at hqu hqv
  simp only [CollisionForm.rawDifference,WeightedPhysicalForm.weightedDifference,
    PhysicalMarginal.completeDifference,hqu,hqv]

theorem actual_rj_collision_form {R : ℝ} (hR : 0<R) {θ : Thermodynamics.Parameter}
    (hθ : θ∈Thermodynamics.positiveDomain R) (u v : CubeFunction R) :
    cubeIntegral R ((v*inverseCube (rjCube hθ) (fun k=>(rjCube_pos hθ k).ne'))*
      fderiv ℝ (collisionMap R hR.le) (rjCube hθ) (rjCube hθ*u))=
      -physicalForm hR.le hθ (toWeighted hR u) (toWeighted hR v) := by
  rw [rj_fderiv_full_form,toWeighted_form]

def basisCube {R : ℝ} {θ : Thermodynamics.Parameter}
    (hθ : θ∈Thermodynamics.positiveDomain R) (i : Fin 5) : CubeFunction R :=
  ⟨fun k=>PhysicalFiveBasis.basisFunction θ i k,
    continuousOn_iff_continuous_restrict.mp (PhysicalFiveBasis.basis_continuousOn hθ i)⟩

theorem toWeighted_analysis {R : ℝ} (hR : 0<R) {θ : Thermodynamics.Parameter}
    (hθ : θ∈Thermodynamics.positiveDomain R) (u : CubeFunction R) (i : Fin 5) :
    analysisMap hR hθ (toWeighted hR u) i=cubeIntegral R (u*basisCube hθ i) := by
  rw [analysisMap_apply]
  calc
    _=∫k,continuousExtension R u k*basisFunction θ i k∂ActualPairNormalization.cubeVolume R := by
      apply integral_congr_ae
      filter_upwards [toWeighted_ae hR u] with k hk
      rw [hk]
    _=∫k:MomentumDomain R,continuousExtension R u k*basisFunction θ i k∂momentumMeasure R := by
      have hm : MeasurePreserving ((↑):MomentumDomain R→E)
          (momentumMeasure R) (volume.restrict (cube R)) :=
        ⟨measurable_subtype_coe,momentumMeasure_map R⟩
      exact (hm.integral_comp (MeasurableEmbedding.subtype_coe (measurable_cube R))
        (fun k:E=>continuousExtension R u k*basisFunction θ i k)).symm
    _=_ := by
      apply integral_congr_ae
      exact ae_of_all _ fun k=>by
        dsimp only
        rw [continuousExtension_eq R u k]
        rfl

theorem toWeighted_micro {R : ℝ} (hR : 0<R) {θ : Thermodynamics.Parameter}
    (hθ : θ∈Thermodynamics.positiveDomain R) (u : CubeFunction R)
    (hu : ∀i,cubeIntegral R (u*basisCube hθ i)=0) :
    projection hR hθ (toWeighted hR u)=0 := by
  have hz : analysisMap hR hθ (toWeighted hR u)=0 := by
    ext i
    rw [toWeighted_analysis,hu]
    rfl
  simp only [projection,ContinuousLinearMap.comp_apply,hz,map_zero]

/-- Uniform physical H_nu dissipation for the actual C(D) derivative on
every compact positive RJ family and every genuine five-moment-zero test. -/
theorem actual_rj_micro_dissipation {R : ℝ} (hR : 0<R) {K : Set Thermodynamics.Parameter}
    (hK : IsCompact K) (hpos : K⊆Thermodynamics.positiveDomain R) :
    ∃γ:ℝ,0<γ ∧ ∀θ,(hθ:θ∈K)→∀u:CubeFunction R,
      (∀i,cubeIntegral R (u*basisCube (hpos hθ) i)=0)→
      cubeIntegral R ((u*inverseCube (rjCube (hpos hθ))
        (fun k=>(rjCube_pos (hpos hθ) k).ne'))*
          fderiv ℝ (collisionMap R hR.le) (rjCube (hpos hθ)) (rjCube (hpos hθ)*u))
        ≤-γ*‖toWeighted hR u‖^2 := by
  obtain ⟨γ,C,hγ,_hC,hbound⟩:=PhysicalMicroCoercivity.actual_microcoercivity hR hK hpos
  refine ⟨γ,hγ,?_⟩
  intro θ hθ u hu
  rw [actual_rj_collision_form hR (hpos hθ) u u]
  have hg:=(hbound θ hθ (toWeighted hR u) (toWeighted_micro hR (hpos hθ) u hu)).1
  simpa only [neg_mul] using neg_le_neg hg

theorem actual_rj_micro_dissipation_integral {R : ℝ} (hR : 0<R)
    {K : Set Thermodynamics.Parameter} (hK : IsCompact K)
    (hpos : K⊆Thermodynamics.positiveDomain R) :
    ∃γ:ℝ,0<γ ∧ ∀θ,(hθ:θ∈K)→∀u:CubeFunction R,
      (∀i,cubeIntegral R (u*basisCube (hpos hθ) i)=0)→
      cubeIntegral R ((u*inverseCube (rjCube (hpos hθ))
        (fun k=>(rjCube_pos (hpos hθ) k).ne'))*
          fderiv ℝ (collisionMap R hR.le) (rjCube (hpos hθ)) (rjCube (hpos hθ)*u))
        ≤-γ*(∫k:MomentumDomain R,CollisionFrequency.referenceFrequency R k*(u k)^2
          ∂momentumMeasure R) := by
  obtain ⟨γ,hγ,hbound⟩:=actual_rj_micro_dissipation hR hK hpos
  refine ⟨γ,hγ,?_⟩
  intro θ hθ u hu
  simpa only [toWeighted_norm_square hR u] using hbound θ hθ u hu

end
end Resonance.ContinuousWeightedEnergy

#check Resonance.ContinuousWeightedEnergy.toWeighted_ae
#check Resonance.ContinuousWeightedEnergy.toWeighted_norm_square
#check Resonance.ContinuousWeightedEnergy.toWeighted_form
#check Resonance.ContinuousWeightedEnergy.actual_rj_collision_form
#check Resonance.ContinuousWeightedEnergy.toWeighted_analysis
#check Resonance.ContinuousWeightedEnergy.toWeighted_micro
#check Resonance.ContinuousWeightedEnergy.actual_rj_micro_dissipation
#check Resonance.ContinuousWeightedEnergy.actual_rj_micro_dissipation_integral
#print axioms Resonance.ContinuousWeightedEnergy.toWeighted_ae
#print axioms Resonance.ContinuousWeightedEnergy.toWeighted_norm_square
#print axioms Resonance.ContinuousWeightedEnergy.toWeighted_form
#print axioms Resonance.ContinuousWeightedEnergy.actual_rj_collision_form
#print axioms Resonance.ContinuousWeightedEnergy.toWeighted_analysis
#print axioms Resonance.ContinuousWeightedEnergy.toWeighted_micro
#print axioms Resonance.ContinuousWeightedEnergy.actual_rj_micro_dissipation
#print axioms Resonance.ContinuousWeightedEnergy.actual_rj_micro_dissipation_integral
