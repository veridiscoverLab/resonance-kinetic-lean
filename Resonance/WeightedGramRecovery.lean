import Resonance.WeightedMomentGram
import Resonance.FiniteMomentRecovery
import Resonance.PhysicalBasisUniform

/-! The five-dimensional kernel is recovered from the actual moving
weighted moment constraint, uniformly over the original positive compact
RJ family. The multiplier need not be close to one in supremum norm. -/
open Set MeasureTheory
open scoped ENNReal
namespace Resonance.WeightedGramRecovery
noncomputable section
open ResonantMeasure Thermodynamics ReferenceFrequencySpace ActualPairNormalization
open PhysicalFiveBasis PhysicalMomentProjection WeightedMomentGram ActualGramCoercivity
open PhysicalBasisUniform PhysicalFrequencyBounds LpOperators FiniteMomentRecovery

theorem compact_weighted_gram_inverse_bound {R m : ℝ} (hR : 0 < R) (hm : 0 < m)
    {K : Set Parameter} (hK : IsCompact K) (hpos : K⊆positiveDomain R) :
    ∃C : ℝ,0 < C ∧ ∀ θ,(hθ : θ∈K) → ∀ b : E→ℝ,
      ∀ hb : MemLp b ∞ (referenceMeasure R),
      (∀ᵐ k ∂cubeVolume R,m ≤ b k) → ∀ a : Parameter,
        ‖a‖ ≤ C*‖weightedGram hR (hpos hθ) hb a‖ := by
  obtain ⟨lam,hlam,hlo⟩ := compact_original_gram_lower hR hK hpos
  refine ⟨5/(m*lam),by positivity,?_⟩
  intro θ hθ b hb hbm a
  apply coefficient_bound _ (mul_pos hm hlam) _ a
  intro v
  calc
    _ = m*(lam*‖v‖^2) := by ring
    _ ≤ m*gramQuadratic R θ v := mul_le_mul_of_nonneg_left (hlo θ hθ v) hm.le
    _ ≤ _ := weightedGram_lower hR (hpos hθ) hb hbm v

theorem actual_uniform_moment_recovery {R m M : ℝ} (hR : 0 < R) (hm : 0 < m) (hM : 0 ≤ M)
    {K : Set Parameter} (hK : IsCompact K) (hpos : K⊆positiveDomain R) :
    ∃C : ℝ,0 < C ∧ ∀ θ,(hθ : θ∈K) → ∀ b : E→ℝ,
      ∀ hb : MemLp b ∞ (referenceMeasure R),
      (∀ᵐ k ∂cubeVolume R,m ≤ b k ∧ b k ≤ M) → ∀ y u : Space R,
      analysisMap hR (hpos hθ) (multiplyCLM hb y)=0 → analysisMap hR (hpos hθ) u=0 →
      ‖y-u‖ ≤ C*(‖(y-u)-projection hR (hpos hθ) (y-u)‖+
        ‖(multiplyCLM hb-1) u‖) := by
  obtain ⟨lam,hlam,hlo⟩ := compact_original_gram_lower hR hK hpos
  obtain ⟨A,S,hA,hS,hops⟩ := compact_basis_operator_bounds hR hK hpos
  let D : ℝ := 5/(m*lam)
  have hD : 0 < D := by dsimp [D]; positivity
  let C : ℝ := 1+S*D*A*(M+1)
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C,hC,?_⟩
  intro θ hθ b hb hbnd y u hmatch hu
  let B := multiplyCLM hb
  let g := (y-u)-projection hR (hpos hθ) (y-u)
  let a := gramInverse hR (hpos hθ) (analysisMap hR (hpos hθ) (y-u))
  have hdecomp : y-u=g+synthesis hR.le (hpos hθ) a := by
    change y-u=((y-u)-projection hR (hpos hθ) (y-u))+projection hR (hpos hθ) (y-u)
    abel
  have hBlo : ∀ v : Parameter,(m*lam)*‖v‖^2 ≤
      v ⬝ᵥ analysisMap hR (hpos hθ) (B (synthesis hR.le (hpos hθ) v)) := by
    intro v
    calc
      _ = m*(lam*‖v‖^2) := by ring
      _ ≤ m*gramQuadratic R θ v := mul_le_mul_of_nonneg_left (hlo θ hθ v) hm.le
      _ ≤ _ := weightedGram_lower hR (hpos hθ) hb (hbnd.mono (fun _ h=>h.1)) v
  have hB : ‖B‖ ≤ M := by
    apply B.opNorm_le_bound hM
    intro v
    apply multiply_explicit_bound hb ?_ v
    filter_upwards [(reference_volume_equivalent hR).2.ae_le (hbnd.mono (fun _ h=>h.1)),
      (reference_volume_equivalent hR).2.ae_le (hbnd.mono (fun _ h=>h.2))] with k hlo hup
    rw [Real.norm_eq_abs,abs_of_pos (lt_of_lt_of_le hm hlo)]
    exact hup
  have h := recovery_bound (analysisMap hR (hpos hθ)) B (synthesis hR.le (hpos hθ))
    (mul_pos hm hlam) hBlo y u g a hdecomp hmatch hu
  have hmain : ‖y-u‖ ≤ ‖g‖+S*D*(A*M*‖g‖+A*‖(B-1) u‖) := by
    apply h.trans
    change ‖g‖+‖synthesis hR.le (hpos hθ)‖*D*
      (‖analysisMap hR (hpos hθ)‖*‖B‖*‖g‖+‖analysisMap hR (hpos hθ)‖*‖(B-1) u‖) ≤ _
    gcongr
    · exact (hops θ hθ).2
    · exact (hops θ hθ).1
    · exact (hops θ hθ).1
  apply hmain.trans
  change ‖g‖+S*D*(A*M*‖g‖+A*‖(B-1) u‖) ≤ C*(‖g‖+‖(B-1) u‖)
  dsimp [C]
  have hn : 0 ≤ S*D*A*‖g‖+(1+S*D*A*M)*‖B u-u‖ := by positivity
  change ‖g‖+S*D*(A*M*‖g‖+A*‖B u-u‖) ≤ (1+S*D*A*(M+1))*(‖g‖+‖B u-u‖)
  nlinarith only [hn]

end
end Resonance.WeightedGramRecovery
