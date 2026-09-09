import Resonance.ContinuousSourceCoordinates

/-! Continuous microscopic coordinates and their actual bounded
multipliers act on the same original H_nu source representative. -/
open Set MeasureTheory
open scoped ENNReal
namespace Resonance.ContinuousSourceMultiplication
noncomputable section
open ResonantMeasure ReferenceFrequencySpace ActualPairNormalization CubeLinftyCoordinates
open ContinuousSourceCoordinates LpOperators

def multiplier {R : ℝ} (hR : 0 < R) (b : C(cube R,ℝ)) : Space R→L[ℝ]Space R :=
  multiplyCLM (StrongBoundedCell.source_memLp_reference hR (embed R b))

theorem multiplier_original_ae {R : ℝ} (hR : 0 < R) (b : C(cube R,ℝ)) (u : Space R) :
    (multiplier hR b u : E→ℝ)=ᵐ[cubeVolume R] (fun k=>u k*zeroExtension R b k) := by
  have h := (reference_volume_equivalent hR).1.ae_eq
    (multiply_ae (StrongBoundedCell.source_memLp_reference hR (embed R b)) u)
  filter_upwards [h,embed_ae R b] with k hk hb
  exact hk.trans (congrArg (fun v=>u k*v) hb)

theorem multiplier_sourceMap {R : ℝ} (hR : 0 < R) (b f : C(cube R,ℝ)) :
    multiplier hR b (sourceMap hR f)=sourceMap hR (b*f) := by
  apply Lp.ext
  apply (reference_volume_equivalent hR).2.ae_eq
  filter_upwards [multiplier_original_ae hR b (sourceMap hR f),sourceMap_ae hR f,
    sourceMap_ae hR (b*f),ae_restrict_mem (measurable_cube R)] with k hb hf hbf hk
  rw [hb,hf,hbf,zeroExtension_apply R f ⟨k,hk⟩,zeroExtension_apply R b ⟨k,hk⟩,
    zeroExtension_apply R (b*f) ⟨k,hk⟩,ContinuousMap.mul_apply,mul_comm]

theorem multiplier_cube_bounds {R : ℝ} (b : C(cube R,ℝ)) {m M : ℝ}
    (hb : ∀ k,m ≤ b k ∧ b k ≤ M) :
    ∀ᵐ k ∂cubeVolume R,m ≤ embed R b k ∧ embed R b k ≤ M := by
  filter_upwards [embed_ae R b,ae_restrict_mem (measurable_cube R)] with k he hk
  rw [he,zeroExtension_apply R b ⟨k,hk⟩]
  exact hb ⟨k,hk⟩

end
end Resonance.ContinuousSourceMultiplication
