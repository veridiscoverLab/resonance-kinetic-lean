import Resonance.ActualMatchedMoments
import Resonance.EulerCoefficients

/-! Exact five-moment equation of the actual matched parameter. The remainder
is the flux of the same f-N, not a separate constitutive input or error bound. -/
open Set MeasureTheory
open scoped BigOperators
namespace Resonance.MatchedMomentEquation
noncomputable section
open FreeTransport JetCollision SpatialChainRule SpatialJetSpace
open ContinuousCollisionMoments JetMomentDynamics ActualMatchedMoments
open Thermodynamics ThermodynamicChart WeightedPhysicalForm WeightedJointMeasure PhaseEnergy
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 30000

def fluxVector (R : ℝ) (j : Fin 3) : CubeFunction R →L[ℝ] Parameter :=
  ContinuousLinearMap.pi (fun i => fluxMoment R (basisParameter i) j)

theorem fluxVector_integral (R : ℝ) (j : Fin 3) (f : CubeFunction R) (i : Fin 5) :
    fluxVector R j f i=∫ k,(2*(k : ResonantMeasure.E) j)*
      Entropy.fiveInvariants i (coordinates k)*f k ∂momentumMeasure R := by
  change fluxMoment R (basisParameter i) j f=_
  rw [fluxMoment_integral]
  simp_rw [basis_reciprocal]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun k => by ring

def actualFlux (R : ℝ) (f : Distribution R) (j : Fin 3) : C(SpatialTorus,Parameter) :=
  ⟨fun X => fluxVector R j (f.curry X),(fluxVector R j).continuous.comp f.curry.continuous⟩

theorem rjCube_flux (R : ℝ) (θ : Parameter) (hθ : θ∈positiveDomain R) (j : Fin 3) :
    fluxVector R j (rjCube R θ hθ)=EulerCoefficients.fluxMap R j θ := by
  ext i
  rw [fluxVector_integral,EulerCoefficients.fluxMap_integral]
  have hm : MeasurePreserving ((↑) : MomentumDomain R → ResonantMeasure.E)
      (momentumMeasure R) (volume.restrict (ResonantMeasure.cube R)) :=
    ⟨measurable_subtype_coe,momentumMeasure_map R⟩
  calc
    (∫ k : MomentumDomain R,(2*(k : ResonantMeasure.E) j)*
        Entropy.fiveInvariants i (coordinates k)*rjCube R θ hθ k ∂momentumMeasure R) =
        ∫ k in ResonantMeasure.cube R,(2*k j)*Entropy.fiveInvariants i (coordinates k)*profile θ k :=
      hm.integral_comp (MeasurableEmbedding.subtype_coe (ResonantMeasure.measurable_cube R))
        (fun k : ResonantMeasure.E => (2*k j)*Entropy.fiveInvariants i (coordinates k)*profile θ k)
    _ = ∫ k,(2*k j)*Entropy.fiveInvariants i k*Entropy.rj Entropy.fiveInvariants θ k
        ∂Entropy.cubeMeasure R := by
      have hF : AEStronglyMeasurable (fun k : ResonantMeasure.E =>
          (2*k j)*Entropy.fiveInvariants i (coordinates k)*profile θ k)
          (volume.restrict (ResonantMeasure.cube R)) := by
        apply Measurable.aestronglyMeasurable
        exact ((continuous_const.mul ((continuous_apply j).comp coordinates_continuous)).measurable.mul
          ((Entropy.fiveInvariants_continuous i).comp coordinates_continuous).measurable).mul
          (profile_measurable θ)
      exact CoareaNormalization.thermodynamic_cube_integral R _ hF

def microFlux (R : ℝ) (hR : 0<R) (f : Distribution R) (j : Fin 3) (X : SpatialTorus) :
    Parameter := actualFlux R f j X-EulerCoefficients.fluxMap R j (matchedValue R hR f X)

theorem microFlux_same_difference (R : ℝ) (hR : 0<R) (f : Distribution R)
    (j : Fin 3) (X : SpatialTorus) (hX : actualMoments R f X∈momentImage R) :
    microFlux R hR f j X=fluxVector R j
      (f.curry X-rjCube R (matchedValue R hR f X) (matched_positive R hR f X hX)) := by
  rw [map_sub,rjCube_flux]
  rfl

theorem actualFlux_hasFDerivAt (R : ℝ) (p : Space R) (j : Fin 3) (x : RealPosition) :
    HasFDerivAt (fun y => actualFlux R (readback p) j (torusQuotient y))
      ((fluxVector R j).comp (p.val.2.1 (torusQuotient x))) x :=
  (fluxVector R j).hasFDerivAt.comp x (p.property.1 x)

theorem full_flux_divergence (R : ℝ) (p : Space R) (x : RealPosition) :
    (∑ j : Fin 3,fderiv ℝ (fun y => actualFlux R (readback p) j (torusQuotient y)) x
      (Pi.single j 1))=divergenceVector R p x := by
  ext i
  simp only [Finset.sum_apply,divergenceVector,fluxDivergence]
  apply Finset.sum_congr rfl
  intro j _
  rw [(actualFlux_hasFDerivAt R p j x).fderiv,(flux_hasFDerivAt R (basisParameter i) j p x).fderiv]
  rfl

def microFluxDivergence (R : ℝ) (hR : 0<R) (p : Space R) (x : RealPosition) : Parameter :=
  ∑ j : Fin 3,fderiv ℝ (fun y => microFlux R hR (readback p) j (torusQuotient y)) x
    (Pi.single j 1)

def eulerGradient (R : ℝ) (hR : 0<R) (p : Space R) (x : RealPosition) : Parameter :=
  ∑ j : Fin 3,(EulerCoefficients.fluxMatrix R j
      (matchedValue R hR (readback p) (torusQuotient x))).mulVec
    (matchedSpatialDerivative R hR p x (Pi.single j 1))

theorem microFlux_hasFDerivAt (R : ℝ) (hR : 0<R) (p : Space R) (j : Fin 3) (x : RealPosition)
    (hx : actualMoments R (readback p) (torusQuotient x)∈momentImage R) :
    HasFDerivAt (fun y => microFlux R hR (readback p) j (torusQuotient y))
      (((fluxVector R j).comp (p.val.2.1 (torusQuotient x)))-
        (EulerCoefficients.fluxDerivative R j
          (matchedValue R hR (readback p) (torusQuotient x))).comp
            (matchedSpatialDerivative R hR p x)) x := by
  have hθ := (matched_real_contDiffAt R hR p x hx).differentiableAt (by norm_num)
  have hn := (EulerCoefficients.fluxMap_hasFDerivAt R j
    (matchedValue R hR (readback p) (torusQuotient x))
    (matched_positive R hR (readback p) (torusQuotient x) hx)).comp x hθ.hasFDerivAt
  exact (actualFlux_hasFDerivAt R p j x).sub hn

theorem microFlux_divergence_identity (R : ℝ) (hR : 0<R) (p : Space R) (x : RealPosition)
    (hx : actualMoments R (readback p) (torusQuotient x)∈momentImage R) :
    microFluxDivergence R hR p x=divergenceVector R p x+eulerGradient R hR p x := by
  rw [←full_flux_divergence]
  ext i
  simp only [microFluxDivergence,eulerGradient,Pi.add_apply,Finset.sum_apply,←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  rw [(microFlux_hasFDerivAt R hR p j x hx).fderiv,(actualFlux_hasFDerivAt R p j x).fderiv]
  simp only [ContinuousLinearMap.sub_apply,ContinuousLinearMap.comp_apply,Pi.sub_apply,
    EulerCoefficients.fluxDerivative_apply,sub_neg_eq_add]

/-- The actual matched nonlinear moment equation. Its right side is exactly
the divergence of the original f-N flux, with no smallness or closure input. -/
theorem actual_five_moment_macro_equation {R T : ℝ} (hR : 0<R) (hT : 0≤T)
    (c : ℝ) (p₀ : Space R) (p : ℝ→Space R) (hp : ContinuousOn p (Icc 0 T))
    (he : ∀ t∈Icc 0 T,readback (p t)=transport R t (readback p₀)+
      ∫ s in (0 : ℝ)..t,c • transport R (t-s)
        (SpatialCollision.collision R hR.le (readback (p s))))
    (x : RealPosition) {t : ℝ} (ht : t∈Icc 0 T)
    (hx : actualMoments R (readback (p t)) (torusQuotient x)∈momentImage R) :
    ∃ θt : Parameter,
      HasDerivWithinAt (fun τ => matchedValue R hR (readback (p τ)) (torusQuotient x))
        θt (Icc 0 T) t ∧
      (gramMatrix R (matchedValue R hR (readback (p t)) (torusQuotient x))).mulVec θt+
        eulerGradient R hR (p t) x=microFluxDivergence R hR (p t) x := by
  obtain ⟨θt,hd,hg⟩ := actual_matched_gram_equation hR hT c p₀ p hp he x ht hx
  refine ⟨θt,hd,?_⟩
  rw [hg,microFlux_divergence_identity R hR (p t) x hx]

#check fluxVector_integral
#check rjCube_flux
#check microFlux_same_difference
#check actualFlux_hasFDerivAt
#check full_flux_divergence
#check microFlux_hasFDerivAt
#check microFlux_divergence_identity
#check actual_five_moment_macro_equation
#print axioms fluxVector_integral
#print axioms rjCube_flux
#print axioms microFlux_same_difference
#print axioms actualFlux_hasFDerivAt
#print axioms full_flux_divergence
#print axioms microFlux_hasFDerivAt
#print axioms microFlux_divergence_identity
#print axioms actual_five_moment_macro_equation

end
end Resonance.MatchedMomentEquation
