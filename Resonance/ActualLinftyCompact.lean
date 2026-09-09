import Resonance.ActualFrequencyRatio
import Resonance.LinftyRowMultiplier
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousFunctions

/-! The actual two normalized pair terms map L-infinity into C(D) compactly.
Both source-side vanishing frequencies are retained.  The final signed
operator is the original incoming term minus twice the cross term. -/
open MeasureTheory Set Filter
open scoped ENNReal Topology
namespace Resonance.ActualLinftyCompact
noncomputable section
set_option maxHeartbeats 1000000
open ResonantMeasure CollisionFrequency WeightedJointMeasure
open ActualReferenceRowOperator ActualFrequencyRatio

instance cubeMeasure_finite (R : ℝ) : IsFiniteMeasure (cubeMeasure R) := by
  letI : IsFiniteMeasureOnCompacts (cubeMeasure R) :=
    IsFiniteMeasureOnCompacts.comap' volume continuous_subtype_val
      (MeasurableEmbedding.subtype_coe (FiberContinuity.cube_isClosed R).measurableSet)
  infer_instance

def continuousToLinfty (R : ℝ) : C(cube R,ℝ) →L[ℝ] Lp ℝ ∞ (cubeMeasure R) :=
  ContinuousMap.toLp ∞ (cubeMeasure R) ℝ

theorem continuousToLinfty_ae (R : ℝ) (f : C(cube R,ℝ)) :
    continuousToLinfty R f =ᵐ[cubeMeasure R] f :=
  ContinuousMap.coeFn_toLp (cubeMeasure R) f

def rawRow (R : ℝ) (r : E×E → ℝ≥0∞) (k p : cube R) : ℝ :=
  (referenceFrequency R p)⁻¹*(r ((k:E),(p:E))).toReal

def pairKernel (R : ℝ) (θ : Thermodynamics.Parameter) (r : E×E → ℝ≥0∞)
    (k p : cube R) : ℝ :=
  (r ((k:E),(p:E))).toReal/(profile θ k*profile θ p*lossFrequency R (profile θ) p)

theorem normalization_identity {R : ℝ} (θ : Thermodynamics.Parameter)
    (r : E×E → ℝ≥0∞) (k p : cube R) (hp : referenceFrequency R p ≠ 0) :
    (profile θ k)⁻¹*(rawRow R r k p*inputRatio R θ p)=pairKernel R θ r k p := by
  unfold rawRow inputRatio pairKernel
  simp only [div_eq_mul_inv,mul_inv]
  calc
    _ = ((referenceFrequency R p)⁻¹*referenceFrequency R p)*
        ((r ((k:E),(p:E))).toReal*((profile θ k)⁻¹*(profile θ p)⁻¹*
          (lossFrequency R (profile θ) p)⁻¹)) := by ring
    _ = _ := by rw [inv_mul_cancel₀ hp,one_mul]

theorem normalized_pair_compact {R : ℝ} (hR : 0 < R)
    {θ : Thermodynamics.Parameter} (hθ : θ ∈ Thermodynamics.positiveDomain R)
    (r : E×E → ℝ≥0∞)
    (hi : ∀ k, Integrable (rawRow R r k) (cubeMeasure R))
    (hc : ∀ k, Tendsto (fun a => ∫ p, ‖rawRow R r a p-rawRow R r k p‖ ∂cubeMeasure R)
      (𝓝 k) (𝓝 0)) :
    ∃ T : Lp ℝ ∞ (cubeMeasure R) →L[ℝ] C(cube R,ℝ), IsCompactOperator T ∧
      ∀ f k, Integrable (fun p => pairKernel R θ r k p*f p) (cubeMeasure R) ∧
        T f k = ∫ p, pairKernel R θ r k p*f p ∂cubeMeasure R := by
  obtain ⟨B,hB,hbound⟩ := inputRatio_bounded hR hθ
  have hbm : AEStronglyMeasurable (fun p : cube R => inputRatio R θ p) (cubeMeasure R) :=
    ((inputRatio_measurable R θ).comp measurable_subtype_coe).aestronglyMeasurable
  have hb : ∀ᵐ p : cube R ∂cubeMeasure R, ‖inputRatio R θ p‖ ≤ B :=
    ae_of_all _ (fun p => hbound p p.property)
  obtain ⟨T,hT,hread⟩ := LinftyRowMultiplier.exists_compact_mul_operator (rawRow R r) hi hc
    (fun p : cube R => inputRatio R θ p) hbm hB.le hb (inverseProfile hθ)
  have hn : ∀ᵐ p : cube R ∂cubeMeasure R, referenceFrequency R p ≠ 0 :=
    ((ae_restrict_iff_subtype (FiberContinuity.cube_isClosed R).measurableSet).mp
      (CornerInverseFrequency.referenceFrequency_positive_ae hR)).mono (fun _ hp => hp.ne')
  refine ⟨T,hT,?_⟩
  intro f k
  have heq : (fun p : cube R => (profile θ k)⁻¹*((rawRow R r k p*inputRatio R θ p)*f p))
      =ᵐ[cubeMeasure R] (fun p => pairKernel R θ r k p*f p) := by
    filter_upwards [hn] with p hp
    rw [← mul_assoc,normalization_identity θ r k p hp]
  have hprod : Integrable (fun p : cube R =>
      (rawRow R r k p*inputRatio R θ p)*f p) (cubeMeasure R) :=
    LinftyRowOperator.product_integrable (fun k p : cube R => rawRow R r k p*inputRatio R θ p)
      (ContinuousRowMultiplier.mul_rows_integrable (rawRow R r) hi _ hbm hb) f k
  refine ⟨(hprod.const_mul ((profile θ k)⁻¹)).congr heq,?_⟩
  rw [hread]
  change (profile θ k)⁻¹*(∫ p, (rawRow R r k p*inputRatio R θ p)*f p ∂cubeMeasure R)=_
  rw [← integral_const_mul]
  exact integral_congr_ae heq

theorem incoming_compact_to_continuous {R : ℝ} (hR : 0 < R)
    {θ : Thermodynamics.Parameter} (hθ : θ ∈ Thermodynamics.positiveDomain R) :
    ∃ T : Lp ℝ ∞ (cubeMeasure R) →L[ℝ] C(cube R,ℝ), IsCompactOperator T ∧
      ∀ f k, Integrable (fun p => pairKernel R θ
          (IncomingPairDensity.density R (weight θ)) k p*f p) (cubeMeasure R) ∧
        T f k = ∫ p, pairKernel R θ (IncomingPairDensity.density R (weight θ)) k p*f p
          ∂cubeMeasure R :=
  normalized_pair_compact hR hθ _ (incomingRow_integrable hR hθ) (incomingRow_L1_continuous hR hθ)

theorem cross_compact_to_continuous {R : ℝ} (hR : 0 < R)
    {θ : Thermodynamics.Parameter} (hθ : θ ∈ Thermodynamics.positiveDomain R) :
    ∃ T : Lp ℝ ∞ (cubeMeasure R) →L[ℝ] C(cube R,ℝ), IsCompactOperator T ∧
      ∀ f k, Integrable (fun p => pairKernel R θ
          (CrossPairDensity.density R (weight θ)) k p*f p) (cubeMeasure R) ∧
        T f k = ∫ p, pairKernel R θ (CrossPairDensity.density R (weight θ)) k p*f p
          ∂cubeMeasure R :=
  normalized_pair_compact hR hθ _ (crossRow_integrable hR hθ) (crossRow_L1_continuous hR hθ)

def signedKernel (R : ℝ) (θ : Thermodynamics.Parameter) (k p : cube R) : ℝ :=
  pairKernel R θ (IncomingPairDensity.density R (weight θ)) k p-
    2*pairKernel R θ (CrossPairDensity.density R (weight θ)) k p

theorem actual_signed_compact_to_continuous {R : ℝ} (hR : 0 < R)
    {θ : Thermodynamics.Parameter} (hθ : θ ∈ Thermodynamics.positiveDomain R) :
    ∃ T : Lp ℝ ∞ (cubeMeasure R) →L[ℝ] C(cube R,ℝ), IsCompactOperator T ∧
      ∀ f k, Integrable (fun p => signedKernel R θ k p*f p) (cubeMeasure R) ∧
        T f k = ∫ p, signedKernel R θ k p*f p ∂cubeMeasure R := by
  obtain ⟨T₁,hT₁,h₁⟩ := incoming_compact_to_continuous hR hθ
  obtain ⟨T₂,hT₂,h₂⟩ := cross_compact_to_continuous hR hθ
  refine ⟨T₁-(2:ℝ) • T₂,hT₁.sub (hT₂.smul 2),?_⟩
  intro f k
  have heq (p : cube R) : signedKernel R θ k p*f p=
      pairKernel R θ (IncomingPairDensity.density R (weight θ)) k p*f p-
        2*(pairKernel R θ (CrossPairDensity.density R (weight θ)) k p*f p) := by
    unfold signedKernel; ring
  constructor
  · simp_rw [heq]
    exact (h₁ f k).1.sub ((h₂ f k).1.const_mul 2)
  · change T₁ f k-2*T₂ f k=_
    rw [(h₁ f k).2,(h₂ f k).2]
    simp_rw [heq]
    rw [integral_sub (h₁ f k).1 ((h₂ f k).1.const_mul 2),integral_const_mul]

/-- The same original integral defines a compact L-infinity endomorphism;
the output has the displayed continuous representative. -/
theorem actual_signed_compact_linfty {R : ℝ} (hR : 0 < R)
    {θ : Thermodynamics.Parameter} (hθ : θ ∈ Thermodynamics.positiveDomain R) :
    ∃ T : Lp ℝ ∞ (cubeMeasure R) →L[ℝ] Lp ℝ ∞ (cubeMeasure R), IsCompactOperator T ∧
      ∀ f, ∃ g : C(cube R,ℝ), T f=continuousToLinfty R g ∧
        ∀ k, Integrable (fun p => signedKernel R θ k p*f p) (cubeMeasure R) ∧
          g k = ∫ p, signedKernel R θ k p*f p ∂cubeMeasure R := by
  obtain ⟨S,hS,hread⟩ := actual_signed_compact_to_continuous hR hθ
  exact ⟨(continuousToLinfty R).comp S,hS.clm_comp (continuousToLinfty R),
    fun f => ⟨S f,rfl,hread f⟩⟩

def signedToContinuous {R : ℝ} (hR : 0 < R)
    {θ : Thermodynamics.Parameter} (hθ : θ ∈ Thermodynamics.positiveDomain R) :
    Lp ℝ ∞ (cubeMeasure R) →L[ℝ] C(cube R,ℝ) :=
  Classical.choose (actual_signed_compact_to_continuous hR hθ)

theorem signedToContinuous_compact {R : ℝ} (hR : 0 < R)
    {θ : Thermodynamics.Parameter} (hθ : θ ∈ Thermodynamics.positiveDomain R) :
    IsCompactOperator (signedToContinuous hR hθ) :=
  (Classical.choose_spec (actual_signed_compact_to_continuous hR hθ)).1

theorem signedToContinuous_integrable_apply {R : ℝ} (hR : 0 < R)
    {θ : Thermodynamics.Parameter} (hθ : θ ∈ Thermodynamics.positiveDomain R)
    (f : Lp ℝ ∞ (cubeMeasure R)) (k : cube R) :
    Integrable (fun p => signedKernel R θ k p*f p) (cubeMeasure R) ∧
      signedToContinuous hR hθ f k = ∫ p, signedKernel R θ k p*f p ∂cubeMeasure R :=
  (Classical.choose_spec (actual_signed_compact_to_continuous hR hθ)).2 f k

def signedOperator {R : ℝ} (hR : 0 < R)
    {θ : Thermodynamics.Parameter} (hθ : θ ∈ Thermodynamics.positiveDomain R) :
    Lp ℝ ∞ (cubeMeasure R) →L[ℝ] Lp ℝ ∞ (cubeMeasure R) :=
  (continuousToLinfty R).comp (signedToContinuous hR hθ)

theorem signedOperator_compact {R : ℝ} (hR : 0 < R)
    {θ : Thermodynamics.Parameter} (hθ : θ ∈ Thermodynamics.positiveDomain R) :
    IsCompactOperator (signedOperator hR hθ) :=
  (signedToContinuous_compact hR hθ).clm_comp (continuousToLinfty R)

theorem signedOperator_ae {R : ℝ} (hR : 0 < R)
    {θ : Thermodynamics.Parameter} (hθ : θ ∈ Thermodynamics.positiveDomain R)
    (f : Lp ℝ ∞ (cubeMeasure R)) :
    signedOperator hR hθ f =ᵐ[cubeMeasure R]
      (fun k => ∫ p, signedKernel R θ k p*f p ∂cubeMeasure R) := by
  filter_upwards [continuousToLinfty_ae R (signedToContinuous hR hθ f)] with k hk
  exact hk.trans (signedToContinuous_integrable_apply hR hθ f k).2

theorem actual_signed_compact_continuous {R : ℝ} (hR : 0 < R)
    {θ : Thermodynamics.Parameter} (hθ : θ ∈ Thermodynamics.positiveDomain R) :
    ∃ T : C(cube R,ℝ) →L[ℝ] C(cube R,ℝ), IsCompactOperator T ∧
      ∀ f k, Integrable (fun p => signedKernel R θ k p*f p) (cubeMeasure R) ∧
        T f k = ∫ p, signedKernel R θ k p*f p ∂cubeMeasure R := by
  refine ⟨(signedToContinuous hR hθ).comp (continuousToLinfty R),
    (signedToContinuous_compact hR hθ).comp_clm (continuousToLinfty R),?_⟩
  intro f k
  have heq : (fun p => signedKernel R θ k p*(continuousToLinfty R f) p)
      =ᵐ[cubeMeasure R] (fun p => signedKernel R θ k p*f p) := by
    filter_upwards [continuousToLinfty_ae R f] with p hp
    rw [hp]
  have hread := signedToContinuous_integrable_apply hR hθ (continuousToLinfty R f) k
  exact ⟨hread.1.congr heq,hread.2.trans (integral_congr_ae heq)⟩

end
end Resonance.ActualLinftyCompact
