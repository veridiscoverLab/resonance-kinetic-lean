import Resonance.ActualPairKernels
import Resonance.HilbertSchmidtCompact

/-! Exact bilinear representations of the original cross operators.
The kernel identities come from the same full-quartet pair marginals. -/
open MeasureTheory
namespace Resonance.ActualCrossPairing
noncomputable section
open ResonantMeasure WeightedJointMeasure FrequencyWeightedForm FrequencyGramDecomposition
open ActualPairKernels ActualPairNormalization

theorem cross_pair_integral (R : ℝ) (θ : Thermodynamics.Parameter) (i j : Fin 4)
    (f g : H R θ) : inner ℝ f (cross R θ i j g)=
      ∫p,g p.2*f p.1∂(jointMeasure R θ).map (fun q=>(q i,q j)) := by
  have hm : Measurable (fun p : E×E=>g p.2*f p.1) :=
    ((Lp.stronglyMeasurable g).measurable.comp measurable_snd).mul
      ((Lp.stronglyMeasurable f).measurable.comp measurable_fst)
  rw [cross_pairing,L2.inner_def,integral_map
    ((measurable_pi_apply i).prodMk (measurable_pi_apply j)).aemeasurable hm.aestronglyMeasurable]
  apply integral_congr_ae
  filter_upwards [pullback_ae R θ i f,pullback_ae R θ j g] with q hf hg
  change (pullback R θ j g) q*(pullback R θ i f) q=g (q j)*f (q i)
  rw [hf,hg]

theorem cross_kernel_integral (R : ℝ) (θ : Thermodynamics.Parameter) (i j : Fin 4)
    {K : E×E→ℝ} (hK : Measurable K) (hKn : ∀p,0≤K p)
    (hpair : (jointMeasure R θ).map (fun q=>(q i,q j))=
      ((marginal R θ).prod (marginal R θ)).withDensity (fun p=>ENNReal.ofReal (K p)))
    (f g : H R θ) : inner ℝ f (cross R θ i j g)=
      ∫p,K p*g p.2*f p.1∂(marginal R θ).prod (marginal R θ) := by
  rw [cross_pair_integral,hpair,integral_withDensity_eq_integral_toReal_smul
    hK.ennreal_ofReal (ae_of_all _ (fun _=>ENNReal.ofReal_lt_top))]
  apply integral_congr_ae
  apply ae_of_all
  intro p
  dsimp only
  rw [ENNReal.toReal_ofReal (hKn p),smul_eq_mul]
  exact (mul_assoc _ _ _).symm

theorem kernel01_measurable (R : ℝ) (θ : Thermodynamics.Parameter) :
    Measurable (kernel01 R θ) :=
  NormalizedPairDensity.realKernel_measurable (marginalDensity_measurable R θ)
    (marginalDensity_measurable R θ) (IncomingPairDensity.density_measurable R (weight_measurable θ))

theorem kernel02_measurable (R : ℝ) (θ : Thermodynamics.Parameter) :
    Measurable (kernel02 R θ) :=
  NormalizedPairDensity.realKernel_measurable (marginalDensity_measurable R θ)
    (marginalDensity_measurable R θ) (CrossPairDensity.density_measurable R (weight_measurable θ))

theorem kernel01_represents {R : ℝ} (hR : 0<R) {θ : Thermodynamics.Parameter}
    (hθ : θ∈Thermodynamics.positiveDomain R) (f g : H R θ) :
    inner ℝ f (cross R θ 0 1 g)=
      ∫p,kernel01 R θ p*g p.2*f p.1∂(marginal R θ).prod (marginal R θ) :=
  cross_kernel_integral R θ 0 1 (kernel01_measurable R θ)
    (fun _=>ENNReal.toReal_nonneg) (incoming_pair_normalized hR hθ) f g

theorem kernel02_represents {R : ℝ} (hR : 0<R) {θ : Thermodynamics.Parameter}
    (hθ : θ∈Thermodynamics.positiveDomain R) (f g : H R θ) :
    inner ℝ f (cross R θ 0 2 g)=
      ∫p,kernel02 R θ p*g p.2*f p.1∂(marginal R θ).prod (marginal R θ) :=
  cross_kernel_integral R θ 0 2 (kernel02_measurable R θ)
    (fun _=>ENNReal.toReal_nonneg) (cross_pair_normalized hR hθ) f g

theorem cross01_compact_of_kernel_memLp {R : ℝ} (hR : 0<R) {θ : Thermodynamics.Parameter}
    (hθ : θ∈Thermodynamics.positiveDomain R)
    (hK : MemLp (kernel01 R θ) 2 ((marginal R θ).prod (marginal R θ))) :
    IsCompactOperator (cross R θ 0 1) := by
  letI := jointMeasure_finite hR.le hθ
  letI : IsFiniteMeasure (marginal R θ) := inferInstanceAs
    (IsFiniteMeasure ((jointMeasure R θ).map (fun q=>q 0)))
  exact HilbertSchmidtCompact.isCompactOperator_of_memLp_kernel (marginal R θ) (marginal R θ)
    hK (fun u v=>kernel01_represents hR hθ v u)

theorem cross02_compact_of_kernel_memLp {R : ℝ} (hR : 0<R) {θ : Thermodynamics.Parameter}
    (hθ : θ∈Thermodynamics.positiveDomain R)
    (hK : MemLp (kernel02 R θ) 2 ((marginal R θ).prod (marginal R θ))) :
    IsCompactOperator (cross R θ 0 2) := by
  letI := jointMeasure_finite hR.le hθ
  letI : IsFiniteMeasure (marginal R θ) := inferInstanceAs
    (IsFiniteMeasure ((jointMeasure R θ).map (fun q=>q 0)))
  exact HilbertSchmidtCompact.isCompactOperator_of_memLp_kernel (marginal R θ) (marginal R θ)
    hK (fun u v=>kernel02_represents hR hθ v u)

end
end Resonance.ActualCrossPairing
