import Resonance.BoundedSourceMaps
import Resonance.ProfileBanachSmooth
import Resonance.ContinuousCollisionMoments

/-! Continuous functions on the actual closed cube embed into the fixed
reference-frequency Hilbert space. The five-coordinate analysis is the
original unweighted volume moment of N times that same function. -/
open Set MeasureTheory
open scoped ENNReal BigOperators
namespace Resonance.ContinuousSourceCoordinates
noncomputable section
set_option maxHeartbeats 2000000
open ResonantMeasure Thermodynamics ProfileBanachSmooth
open CubeLinftyCoordinates ActualPairNormalization PhysicalFiveBasis PhysicalMomentProjection

def sourceMap {R : ℝ} (hR : 0<R) :
    C(cube R,ℝ)→L[ℝ]ReferenceFrequencySpace.Space R :=
  (BoundedSourceMaps.sourceMap hR).comp (embed R)

theorem sourceMap_apply {R : ℝ} (hR : 0<R) (f : C(cube R,ℝ)) :
    sourceMap hR f=StrongBoundedCell.sourceVector hR (embed R f) := rfl

theorem sourceMap_ae {R : ℝ} (hR : 0<R) (f : C(cube R,ℝ)) :
    (sourceMap hR f : E→ℝ)=ᵐ[cubeVolume R] zeroExtension R f :=
  (BoundedSourceMaps.sourceVector_ae hR (embed R f)).trans (embed_ae R f)

theorem sourceMap_reference_ae {R : ℝ} (hR : 0<R) (f : C(cube R,ℝ)) :
    (sourceMap hR f : E→ℝ)=ᵐ[ReferenceFrequencySpace.referenceMeasure R] zeroExtension R f :=
  (ReferenceFrequencySpace.reference_volume_equivalent hR).2.ae_eq (sourceMap_ae hR f)

theorem sourceMap_bound {R : ℝ} (hR : 0<R) (f : C(cube R,ℝ)) :
    ‖sourceMap hR f‖≤‖BoundedSourceMaps.constantVector hR‖*‖f‖ := by
  exact (BoundedSourceMaps.sourceVector_bound hR (embed R f)).trans
    (mul_le_mul_of_nonneg_left (extendVector_bound R f) (norm_nonneg _))

theorem basis_reciprocal (i : Fin 5) (k : E) :
    WeightedPhysicalForm.reciprocalProfile (Pi.single i 1) k=CoareaNormalization.euclideanFive i k := by
  simp only [WeightedPhysicalForm.reciprocalProfile,Entropy.denominator,
    Pi.single_apply,ite_mul,one_mul,zero_mul,Finset.sum_ite_eq',Finset.mem_univ,if_true]
  exact (CoareaNormalization.euclideanFive_coordinate i (WeightedJointMeasure.coordinates k)).symm

theorem analysis_source_embed {R : ℝ} (hR : 0<R) {θ : Parameter}
    (hθ : θ∈positiveDomain R) (f : C(cube R,ℝ)) (i : Fin 5) :
    analysisMap hR hθ (sourceMap hR f) i=
      ContinuousCollisionMoments.moment R (Pi.single i 1) (profileMap R θ*f) := by
  rw [analysisMap_apply]
  have hm : MeasurePreserving ((↑) : FreeTransport.MomentumDomain R→E)
      (PhaseEnergy.momentumMeasure R) (cubeVolume R) :=
    ⟨measurable_subtype_coe,PhaseEnergy.momentumMeasure_map R⟩
  calc
    _ = ∫k,zeroExtension R f k*basisFunction θ i k∂cubeVolume R := by
      apply integral_congr_ae
      filter_upwards [sourceMap_ae hR f] with k hf
      rw [hf]
    _ = ∫k : FreeTransport.MomentumDomain R,zeroExtension R f k*basisFunction θ i k∂PhaseEnergy.momentumMeasure R :=
      (hm.integral_comp (MeasurableEmbedding.subtype_coe (measurable_cube R)) _).symm
    _ = _ := by
      rw [ContinuousCollisionMoments.moment_integral]
      apply integral_congr_ae
      apply ae_of_all
      intro k
      change zeroExtension R f k*basisFunction θ i k=
        WeightedPhysicalForm.reciprocalProfile (Pi.single i 1) k*(profileMap R θ*f) k
      rw [zeroExtension_apply,basis_reciprocal]
      simp only [ContinuousMap.mul_apply,profileMap_apply hθ,basisFunction]
      ring

theorem sourceMap_micro_iff {R : ℝ} (hR : 0<R) {θ : Parameter}
    (hθ : θ∈positiveDomain R) (f : C(cube R,ℝ)) :
    analysisMap hR hθ (sourceMap hR f)=0 ↔
      ∀i : Fin 5,ContinuousCollisionMoments.moment R (Pi.single i 1) (profileMap R θ*f)=0 := by
  constructor
  · intro h i
    rw [←analysis_source_embed hR hθ,h]
    rfl
  · intro h
    ext i
    rw [analysis_source_embed hR hθ]
    exact h i

end
end Resonance.ContinuousSourceCoordinates
