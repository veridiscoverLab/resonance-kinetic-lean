import Resonance.ActualCrossPairing
import Resonance.LinftyPhysicalDomain
import Resonance.PhysicalWeightedCoercivity

/-! Actual unnormalized pair-density identities.  Integrability is derived
from the common four-leg L² pullbacks before any Fubini or density change. -/
open MeasureTheory
open scoped ENNReal
namespace Resonance.PhysicalPairDensity
noncomputable section
open ResonantMeasure WeightedJointMeasure FrequencyWeightedForm FrequencyGramDecomposition
open ActualPairNormalization ActualPairKernels ActualCrossPairing
open PhysicalFrequencyCoordinates ReferenceFrequencySpace

theorem pair_product_integrable (R : ℝ) (θ : Thermodynamics.Parameter) (i j : Fin 4)
    (f g : H R θ) : Integrable (fun p : E×E=>g p.2*f p.1)
      ((jointMeasure R θ).map (fun q=>(q i,q j))) := by
  have hm : Measurable (fun p : E×E=>g p.2*f p.1) :=
    ((Lp.stronglyMeasurable g).measurable.comp measurable_snd).mul
      ((Lp.stronglyMeasurable f).measurable.comp measurable_fst)
  apply (integrable_map_measure hm.aestronglyMeasurable
    ((measurable_pi_apply i).prodMk (measurable_pi_apply j)).aemeasurable).mpr
  apply (L2.integrable_inner (pullback R θ i f) (pullback R θ j g)).congr
  filter_upwards [pullback_ae R θ i f,pullback_ae R θ j g] with q hf hg
  change (pullback R θ j g) q*(pullback R θ i f) q=g (q j)*f (q i)
  rw [hf,hg]

theorem incoming_pair_cube (R : ℝ) (θ : Thermodynamics.Parameter) :
    (jointMeasure R θ).map (fun q=>(q 0,q 1))=
      ((cubeVolume R).prod (cubeVolume R)).withDensity
        (IncomingPairDensity.density R (weight θ)) := by
  rw [jointMeasure,IncomingPairDensity.weighted_pair_marginal R (weight_measurable θ)]
  exact (restricted_pair_density R
    (fun p hp=>IncomingPairDensity.density_zero_outside R _ hp)).symm

theorem cross_pair_cube {R : ℝ} (hR : 0≤R) (θ : Thermodynamics.Parameter) :
    (jointMeasure R θ).map (fun q=>(q 0,q 2))=
      ((cubeVolume R).prod (cubeVolume R)).withDensity
        (CrossPairDensity.density R (weight θ)) := by
  rw [jointMeasure,CrossPairDensity.weighted_pair_marginal hR (weight_measurable θ)]
  exact (restricted_pair_density R
    (fun p hp=>CrossPairDensity.density_zero_outside R _ hp)).symm

theorem density_pairing (R : ℝ) (θ : Thermodynamics.Parameter) (i j : Fin 4)
    {r : E×E→ℝ≥0∞} (hr : Measurable r) (hrf : ∀p,r p≠∞)
    (hp : (jointMeasure R θ).map (fun q=>(q i,q j))=
      ((cubeVolume R).prod (cubeVolume R)).withDensity r) (f g : H R θ) :
    Integrable (fun p : E×E=> (r p).toReal*g p.2*f p.1)
      ((cubeVolume R).prod (cubeVolume R)) ∧
    inner ℝ f (cross R θ i j g)=
      ∫p,(r p).toReal*g p.2*f p.1∂(cubeVolume R).prod (cubeVolume R) := by
  have hi := pair_product_integrable R θ i j f g
  rw [hp] at hi
  have his := (integrable_withDensity_iff_integrable_smul' hr
    (ae_of_all _ (fun p=>(hrf p).lt_top))).mp hi
  constructor
  · apply his.congr
    exact ae_of_all _ (fun p=>by simp only [smul_eq_mul]; ring)
  · rw [cross_pair_integral,hp,integral_withDensity_eq_integral_toReal_smul
      hr (ae_of_all _ (fun p=>(hrf p).lt_top))]
    apply integral_congr_ae
    exact ae_of_all _ (fun p=>by simp only [smul_eq_mul]; ring)

theorem forward_ae_cube {R : ℝ} (hR : 0<R) {θ : Thermodynamics.Parameter}
    (hθ : θ∈Thermodynamics.positiveDomain R) (u : Space R) :
    forward hR.le hθ u=ᵐ[cubeVolume R] (fun k=>u k/profile θ k) :=
  (cube_marginal_equivalent hR hθ).1.ae_eq (forward_ae hR.le hθ u)

theorem physical_density_pairing {R : ℝ} (hR : 0<R) {θ : Thermodynamics.Parameter}
    (hθ : θ∈Thermodynamics.positiveDomain R) (i j : Fin 4)
    {r : E×E→ℝ≥0∞} (hr : Measurable r) (hrf : ∀p,r p≠∞)
    (hp : (jointMeasure R θ).map (fun q=>(q i,q j))=
      ((cubeVolume R).prod (cubeVolume R)).withDensity r) (u v : Space R) :
    Integrable (fun p : E×E=> (r p).toReal*(u p.2/profile θ p.2)*(v p.1/profile θ p.1))
      ((cubeVolume R).prod (cubeVolume R)) ∧
    inner ℝ (forward hR.le hθ v) (cross R θ i j (forward hR.le hθ u))=
      ∫p,(r p).toReal*(u p.2/profile θ p.2)*(v p.1/profile θ p.1)
        ∂(cubeVolume R).prod (cubeVolume R) := by
  letI := cubeVolume_finite R
  have he : (fun p : E×E=> (r p).toReal*(forward hR.le hθ u) p.2*
      (forward hR.le hθ v) p.1)=ᵐ[(cubeVolume R).prod (cubeVolume R)]
      (fun p=> (r p).toReal*(u p.2/profile θ p.2)*(v p.1/profile θ p.1)) := by
    filter_upwards [Measure.quasiMeasurePreserving_snd.ae_eq (forward_ae_cube hR hθ u),
      Measure.quasiMeasurePreserving_fst.ae_eq (forward_ae_cube hR hθ v)] with p hu hv
    dsimp only [Function.comp_def] at hu hv
    rw [hu,hv]
  obtain ⟨hi,heq⟩ := density_pairing R θ i j hr hrf hp
    (forward hR.le hθ v) (forward hR.le hθ u)
  exact ⟨hi.congr he,heq.trans (integral_congr_ae he)⟩

theorem incoming_physical_pairing {R : ℝ} (hR : 0<R) {θ : Thermodynamics.Parameter}
    (hθ : θ∈Thermodynamics.positiveDomain R) (u v : Space R) :
    Integrable (fun p : E×E=> (IncomingPairDensity.density R (weight θ) p).toReal*
      (u p.2/profile θ p.2)*(v p.1/profile θ p.1))
      ((cubeVolume R).prod (cubeVolume R)) ∧
    inner ℝ (forward hR.le hθ v) (cross R θ 0 1 (forward hR.le hθ u))=
      ∫p,(IncomingPairDensity.density R (weight θ) p).toReal*
        (u p.2/profile θ p.2)*(v p.1/profile θ p.1)
        ∂(cubeVolume R).prod (cubeVolume R) :=
  physical_density_pairing hR hθ 0 1
    (IncomingPairDensity.density_measurable R (weight_measurable θ))
    (incoming_density_finite hθ) (incoming_pair_cube R θ) u v

theorem cross_physical_pairing {R : ℝ} (hR : 0<R) {θ : Thermodynamics.Parameter}
    (hθ : θ∈Thermodynamics.positiveDomain R) (u v : Space R) :
    Integrable (fun p : E×E=> (CrossPairDensity.density R (weight θ) p).toReal*
      (u p.2/profile θ p.2)*(v p.1/profile θ p.1))
      ((cubeVolume R).prod (cubeVolume R)) ∧
    inner ℝ (forward hR.le hθ v) (cross R θ 0 2 (forward hR.le hθ u))=
      ∫p,(CrossPairDensity.density R (weight θ) p).toReal*
        (u p.2/profile θ p.2)*(v p.1/profile θ p.1)
        ∂(cubeVolume R).prod (cubeVolume R) :=
  physical_density_pairing hR hθ 0 2
    (CrossPairDensity.density_measurable R (weight_measurable θ))
    (cross_density_finite hR.le hθ) (cross_pair_cube hR.le θ) u v

end
end Resonance.PhysicalPairDensity
