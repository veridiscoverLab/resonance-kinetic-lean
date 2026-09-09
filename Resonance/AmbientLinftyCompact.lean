import Resonance.CubeLinftyCoordinates

/-! The exact same compact kernel on the ambient restricted-volume
L-infinity space used by the physical weighted collision form. -/
open MeasureTheory Set Filter
open scoped ENNReal Topology
namespace Resonance.AmbientLinftyCompact
noncomputable section
set_option maxHeartbeats 900000
open ResonantMeasure CollisionFrequency WeightedJointMeasure ActualPairNormalization
open ActualReferenceRowOperator ActualLinftyCompact CubeLinftyCoordinates

def kernel (R : ℝ) (θ : Thermodynamics.Parameter) (k p : E) : ℝ :=
  (IncomingPairDensity.density R (weight θ) (k,p)).toReal/
      (profile θ k*profile θ p*lossFrequency R (profile θ) p)-
    2*((CrossPairDensity.density R (weight θ) (k,p)).toReal/
      (profile θ k*profile θ p*lossFrequency R (profile θ) p))

theorem kernel_subtype (R : ℝ) (θ : Thermodynamics.Parameter) (k p : cube R) :
    kernel R θ k p=signedKernel R θ k p := rfl

def continuousOutput {R : ℝ} (hR : 0 < R)
    {θ : Thermodynamics.Parameter} (hθ : θ ∈ Thermodynamics.positiveDomain R) :
    Lp ℝ ∞ (cubeVolume R) →L[ℝ] C(cube R,ℝ) :=
  (signedToContinuous hR hθ).comp (CubeLinftyCoordinates.restrict R).toContinuousLinearMap

theorem continuousOutput_compact {R : ℝ} (hR : 0 < R)
    {θ : Thermodynamics.Parameter} (hθ : θ ∈ Thermodynamics.positiveDomain R) :
    IsCompactOperator (continuousOutput hR hθ) :=
  (signedToContinuous_compact hR hθ).comp_clm
    (CubeLinftyCoordinates.restrict R).toContinuousLinearMap

theorem continuousOutput_integrable_apply {R : ℝ} (hR : 0 < R)
    {θ : Thermodynamics.Parameter} (hθ : θ ∈ Thermodynamics.positiveDomain R)
    (f : Lp ℝ ∞ (cubeVolume R)) (k : cube R) :
    Integrable (fun p => kernel R θ k p*f p) (cubeVolume R) ∧
      continuousOutput hR hθ f k=∫ p,kernel R θ k p*f p ∂cubeVolume R := by
  have hr := signedToContinuous_integrable_apply hR hθ (CubeLinftyCoordinates.restrict R f) k
  have heq : (fun p : cube R => signedKernel R θ k p*(CubeLinftyCoordinates.restrict R f) p)
      =ᵐ[cubeMeasure R] (fun p => kernel R θ k p*f (p:E)) := by
    filter_upwards [restrict_ae R f] with p hp
    rw [hp,kernel_subtype]
  have hi := hr.1.congr heq
  constructor
  · exact (integrableOn_iff_comap_subtypeVal
      (FiberContinuity.cube_isClosed R).measurableSet).mpr hi
  · exact hr.2.trans ((integral_congr_ae heq).trans
      (integral_subtype_comap (FiberContinuity.cube_isClosed R).measurableSet
        (fun p : E => kernel R θ k p*f p)))

def operator {R : ℝ} (hR : 0 < R)
    {θ : Thermodynamics.Parameter} (hθ : θ ∈ Thermodynamics.positiveDomain R) :
    Lp ℝ ∞ (cubeVolume R) →L[ℝ] Lp ℝ ∞ (cubeVolume R) :=
  (CubeLinftyCoordinates.embed R).comp (continuousOutput hR hθ)

theorem operator_compact {R : ℝ} (hR : 0 < R)
    {θ : Thermodynamics.Parameter} (hθ : θ ∈ Thermodynamics.positiveDomain R) :
    IsCompactOperator (operator hR hθ) :=
  (continuousOutput_compact hR hθ).clm_comp (CubeLinftyCoordinates.embed R)

theorem operator_ae {R : ℝ} (hR : 0 < R)
    {θ : Thermodynamics.Parameter} (hθ : θ ∈ Thermodynamics.positiveDomain R)
    (f : Lp ℝ ∞ (cubeVolume R)) :
    operator hR hθ f =ᵐ[cubeVolume R]
      (fun k => ∫ p,kernel R θ k p*f p ∂cubeVolume R) := by
  filter_upwards [embed_ae R (continuousOutput hR hθ f),
    ae_restrict_mem (FiberContinuity.cube_isClosed R).measurableSet] with k he hk
  exact he.trans ((zeroExtension_apply R (continuousOutput hR hθ f) ⟨k,hk⟩).trans
    (continuousOutput_integrable_apply hR hθ f ⟨k,hk⟩).2)

end
end Resonance.AmbientLinftyCompact
