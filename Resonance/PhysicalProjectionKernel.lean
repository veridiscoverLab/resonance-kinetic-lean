import Resonance.PhysicalMomentProjection

/-! Exact equality of the constructed unweighted projection range and the
kernel of the original complete collision form in the fixed physical space. -/
open MeasureTheory Set
open scoped BigOperators
namespace Resonance.PhysicalProjectionKernel
noncomputable section
open ResonantMeasure WeightedJointMeasure Thermodynamics ReferenceFrequencySpace
open PhysicalFiveBasis PhysicalMomentProjection PhysicalFrequencyCoordinates
open QuadraticPointwiseClosure
open CoareaNormalization (euclideanFive)

def parameterCoefficients (b : Parameter) : Coefficients :=
  ⟨b 0,b 1 • (PiLp.proj 2 (fun _ : Fin 3=>ℝ) 0)+
    b 2 • (PiLp.proj 2 (fun _ : Fin 3=>ℝ) 1)+
    b 3 • (PiLp.proj 2 (fun _ : Fin 3=>ℝ) 2),b 4⟩

theorem parameterCoefficients_evaluate (b : Parameter) (k : E) :
    evaluate (parameterCoefficients b) k=Entropy.denominator euclideanFive b k := by
  simp [parameterCoefficients,evaluate,Entropy.denominator,euclideanFive,Fin.sum_univ_succ]
  ring

def coefficientsParameter (b : Coefficients) : Parameter :=
  ![b.1,b.2.1 (ParallelGradientAlgebra.axisPoint 1 0),
    b.2.1 (ParallelGradientAlgebra.axisPoint 1 1),
    b.2.1 (ParallelGradientAlgebra.axisPoint 1 2),b.2.2]

theorem coefficientsParameter_denominator (b : Coefficients) (k : E) :
    Entropy.denominator euclideanFive (coefficientsParameter b) k=evaluate b k := by
  rw [FiveInvariantFinal.evaluate_five_moments]
  simp [coefficientsParameter,Entropy.denominator,euclideanFive,Fin.sum_univ_succ]
  ring

theorem physical_kernel_iff_exists {R : ℝ} (hR : 0<R) {θ : Parameter}
    (hθ : θ∈positiveDomain R) (u : Space R) :
    u∈(physicalDifference hR.le hθ).ker ↔
      ∃b : Coefficients,(u : E→ℝ)=ᵐ[volume.restrict (cube R)]
        (fun k=>profile θ k*evaluate b k) := by
  rw [PhysicalWeightedCoercivity.physical_kernel_classification hR hθ]
  constructor
  · exact ExistsUnique.exists
  · rintro ⟨b,hb⟩
    refine ⟨b,hb,?_⟩
    intro c hc
    apply CollisionCoefficientUniqueness.coefficients_eq_of_ae hR
    rw [←FiveInvariantFinal.cube_restrict_eq_openCube]
    filter_upwards [hc,hb,ae_restrict_mem (measurable_cube R)] with k hck hbk hk
    exact mul_left_cancel₀ (profile_pos hθ hk).ne' (hck.symm.trans hbk)

theorem physical_kernel_eq_synthesis_range {R : ℝ} (hR : 0<R) {θ : Parameter}
    (hθ : θ∈positiveDomain R) :
    (physicalDifference hR.le hθ).ker=(synthesis hR.le hθ).range := by
  ext u
  rw [physical_kernel_iff_exists hR hθ]
  constructor
  · rintro ⟨c,hc⟩
    refine ⟨coefficientsParameter c,?_⟩
    apply Lp.ext
    have hs := synthesis_ae hR.le hθ (coefficientsParameter c)
    have hu := (reference_volume_equivalent hR).2.ae_eq hc
    filter_upwards [hs,hu] with k hsk huk
    exact hsk.trans ((congrArg (fun a=>profile θ k*a)
      (coefficientsParameter_denominator c k)).trans huk.symm)
  · rintro ⟨b,rfl⟩
    refine ⟨parameterCoefficients b,?_⟩
    have hs := (reference_volume_equivalent hR).1.ae_eq (synthesis_ae hR.le hθ b)
    filter_upwards [hs] with k hk
    exact hk.trans (congrArg (fun a=>profile θ k*a) (parameterCoefficients_evaluate b k).symm)

theorem projection_range_eq_kernel {R : ℝ} (hR : 0<R) {θ : Parameter}
    (hθ : θ∈positiveDomain R) :
    (projection hR hθ).range=(physicalDifference hR.le hθ).ker := by
  rw [projection_range,physical_kernel_eq_synthesis_range hR hθ]

theorem projection_fixed_kernel {R : ℝ} (hR : 0<R) {θ : Parameter}
    (hθ : θ∈positiveDomain R) {u : Space R} (hu : u∈(physicalDifference hR.le hθ).ker) :
    projection hR hθ u=u := by
  rw [physical_kernel_eq_synthesis_range hR hθ] at hu
  obtain ⟨b,rfl⟩ := hu
  exact projection_synthesis hR hθ b

theorem projection_difference_zero {R : ℝ} (hR : 0<R) {θ : Parameter}
    (hθ : θ∈positiveDomain R) (u : Space R) :
    physicalDifference hR.le hθ (projection hR hθ u)=0 := by
  have hu : projection hR hθ u∈(projection hR hθ).range := ⟨u,rfl⟩
  rw [projection_range_eq_kernel] at hu
  exact hu

end
end Resonance.PhysicalProjectionKernel
