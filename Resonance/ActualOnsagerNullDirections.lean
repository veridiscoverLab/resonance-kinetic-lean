import Resonance.OnsagerGradientPolynomial

/-! Exact null directions of the original transport quadratic form.
The cancellation of N is only on the original positive sharp cube. -/
open MeasureTheory Set
namespace Resonance.ActualOnsagerNullDirections
noncomputable section
set_option maxHeartbeats 800000
open ResonantMeasure WeightedJointMeasure Thermodynamics
open ActualPairNormalization (cubeVolume)
open PhysicalProjectionKernel ActualOnsagerTensor ActualOnsagerPositive ActualOnsagerKernelBridge
open OnsagerGradientPolynomial
open CoareaNormalization (toMomentumE toMomentumE_cube_preserving)
open QuadraticPointwiseClosure

theorem cube_measure_identity (R : ℝ) :
    Entropy.cubeMeasure R=volume.restrict (OnsagerPolynomial.cube R) := by
  unfold Entropy.cubeMeasure
  congr 1
  ext p
  change ((∀i,-R≤p i) ∧ ∀i,p i≤R) ↔ ∀i∈(univ : Set (Fin 3)),p i∈Icc (-R) R
  simp only [mem_univ,true_implies,mem_Icc]
  exact forall_and.symm

theorem actual_null_directions {R : ℝ} (hR : 0<R) {θ : Parameter}
    (hθ : θ∈positiveDomain R) (a h : Fin 3→ℝ) (B : Fin 3→Fin 3→ℝ) :
    quadraticResponse hR hθ (gradient a B h)=0 ↔ OnsagerPolynomial.nullDirections h B := by
  rw [quadratic_zero_iff_original_invariant]
  constructor
  · rintro ⟨b,hb⟩
    have he : (fun k : E=>MvPolynomial.eval (fun i=>k i) (OnsagerPolynomial.driving a h B))
        =ᵐ[cubeVolume R] (fun k=>MvPolynomial.eval (fun i=>k i)
          (OnsagerPolynomial.invariant b.1 b.2.2
            (fun i=>b.2.1 (ParallelGradientAlgebra.axisPoint 1 i)))) := by
      filter_upwards [hb,ae_restrict_mem (measurable_cube R)] with k hk hkc
      rw [raw_gradient_polynomial,coefficient_polynomial] at hk
      exact mul_left_cancel₀ (profile_pos hθ hkc).ne' hk
    have hp := (toMomentumE_cube_preserving R).quasiMeasurePreserving.ae_eq he
    change (fun p=>MvPolynomial.eval p (OnsagerPolynomial.driving a h B))
      =ᵐ[Entropy.cubeMeasure R] (fun p=>MvPolynomial.eval p
        (OnsagerPolynomial.invariant b.1 b.2.2
          (fun i=>b.2.1 (ParallelGradientAlgebra.axisPoint 1 i)))) at hp
    rw [cube_measure_identity] at hp
    exact (OnsagerPolynomial.cube_null_iff R hR a h B).mp ⟨b.1,b.2.2,_,hp⟩
  · intro hn
    obtain ⟨c,e,l,he⟩ := (OnsagerPolynomial.polynomial_null_iff a h B).mpr hn
    refine ⟨parameterCoefficients ![c,l 0,l 1,l 2,e],ae_of_all _ fun k=>?_⟩
    change rawCombination θ (gradient a B h) k=
      profile θ k*evaluate (parameterCoefficients ![c,l 0,l 1,l 2,e]) k
    rw [raw_gradient_polynomial,polynomial_coefficient,he]

theorem actual_null_scalar_symmetric {R : ℝ} (hR : 0<R) {θ : Parameter}
    (hθ : θ∈positiveDomain R) (a h : Fin 3→ℝ) (B : Fin 3→Fin 3→ℝ) :
    quadraticResponse hR hθ (gradient a B h)=0 ↔
      (∀i,h i=0) ∧ ∃b : ℝ,∀i j,B i j+B j i=if i=j then 2*b else 0 := by
  rw [actual_null_directions,OnsagerPolynomial.nullDirections_iff_scalar_symmetric]

end
end Resonance.ActualOnsagerNullDirections
