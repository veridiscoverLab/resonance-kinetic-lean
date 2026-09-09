import Resonance.CubicParameterCoefficients
import Resonance.ContinuousResolventJets

/-! Every finite RJ parameter derivative of the actual cubic retains
the one-Y estimate. The four coefficient slots are differentiated via a
single bounded evaluation functional, with all collision parents intact. -/
open Set
open scoped ContDiff Topology
namespace Resonance.CubicParameterJets
noncomputable section
set_option maxHeartbeats 2000000
open ResonantMeasure Thermodynamics ProfileBanachSmooth NormalizedCubicOneY
open CubicParameterCoefficients OneWeightedPairReadout OneWeightedParent

def evaluation (R : ℝ) : ContinuousMultilinearMap ℝ (fun _ : Fin 4=>X R) (Coeff R→L[ℝ]X R) :=
  (ContinuousLinearMap.id ℝ (Coeff R)).flipMultilinear

def coefficients (R : ℝ) (θ : Parameter) : Fin 4→X R :=
  ![denominatorMap R θ,profileMap R θ,profileMap R θ,profileMap R θ]

def evaluationFamily (R : ℝ) (θ : Parameter) : Coeff R→L[ℝ]X R :=
  evaluation R (coefficients R θ)

theorem evaluationFamily_apply (R : ℝ) (hR : 0≤R) (θ : Parameter) (u : Fin 3→X R) :
    evaluationFamily R θ (coefficientMap R hR u)=normalizedTrilinear R hR θ u :=
  coefficientMap_normalized R hR θ u

theorem evaluationFamily_contDiffAt {R : ℝ} {θ : Parameter} (hθ : θ∈positiveDomain R) :
    ContDiffAt ℝ ∞ (evaluationFamily R) θ := by
  have hc : ContDiffAt ℝ ∞ (coefficients R) θ := by
    apply contDiffAt_pi.mpr
    intro i
    fin_cases i
    · exact (denominatorMap R).contDiff.contDiffAt
    · exact profileMap_contDiffAt hθ
    · exact profileMap_contDiffAt hθ
    · exact profileMap_contDiffAt hθ
  exact ContDiffAt.comp (g:=fun m : Fin 4→X R=>evaluation R m) (f:=coefficients R) θ
    (ContinuousMultilinearMap.contDiffAt (𝕜:=ℝ) (n:=∞)
      (E:=fun _ : Fin 4=>X R) (F:=Coeff R→L[ℝ]X R) (evaluation R)) hc

theorem evaluationFamily_compact_jet_bound {R : ℝ} {K : Set Parameter}
    (hK : IsCompact K) (hpos : K⊆positiveDomain R) (n : ℕ) :
    ∃C : ℝ,0<C ∧ ∀θ∈K,‖iteratedFDeriv ℝ n (evaluationFamily R) θ‖≤C := by
  have hc : ContinuousOn (fun θ=>iteratedFDeriv ℝ n (evaluationFamily R) θ) K := by
    intro θ hθ
    exact ((evaluationFamily_contDiffAt (hpos hθ)).continuousAt_iteratedFDeriv
      (by exact_mod_cast (show (n:ℕ∞)≤⊤ from le_top))).continuousWithinAt
  obtain ⟨M,hM⟩ := hK.bddAbove_image hc.norm
  refine ⟨max M 0+1,by positivity,?_⟩
  intro θ hθ
  exact (hM ⟨θ,hθ,rfl⟩).trans (by linarith [le_max_left M 0])

theorem actual_normalized_cubic_parameter_jets {R : ℝ} (hR : 0<R)
    {K : Set Parameter} (hK : IsCompact K) (hpos : K⊆positiveDomain R) (n : ℕ) :
    ∃C : ℝ,0<C ∧ ∀θ∈K,∀u : Fin 3→X R,
      ‖iteratedFDeriv ℝ n (fun β=>normalizedTrilinear R hR.le β u) θ‖≤
        C*‖referenceContinuous hR.le*u 0‖*‖u 1‖*‖u 2‖ ∧
      ‖iteratedFDeriv ℝ n (fun β=>normalizedTrilinear R hR.le β u) θ‖≤
        C*‖referenceContinuous hR.le*u 1‖*‖u 0‖*‖u 2‖ ∧
      ‖iteratedFDeriv ℝ n (fun β=>normalizedTrilinear R hR.le β u) θ‖≤
        C*‖referenceContinuous hR.le*u 2‖*‖u 0‖*‖u 1‖ := by
  obtain ⟨A,hA,ha⟩ := evaluationFamily_compact_jet_bound hK hpos n
  refine ⟨4*oneYConstant hR*A,by have hp:=oneYConstant_positive hR; positivity,?_⟩
  intro θ hθ u
  have hb : ‖iteratedFDeriv ℝ n (fun β=>normalizedTrilinear R hR.le β u) θ‖≤
      ‖coefficientMap R hR.le u‖*A := by
    have he : (fun β=>normalizedTrilinear R hR.le β u)=
        (fun β=>evaluationFamily R β (coefficientMap R hR.le u)) := by
      funext β
      exact (evaluationFamily_apply R hR.le β u).symm
    rw [he]
    exact (norm_iteratedFDeriv_clm_apply_const (evaluationFamily_contDiffAt (hpos hθ))
      (c:=coefficientMap R hR.le u)
      (by exact_mod_cast (show (n:ℕ∞)≤⊤ from le_top))).trans
        (mul_le_mul_of_nonneg_left (ha θ hθ) (norm_nonneg _))
  constructor
  · exact hb.trans ((mul_le_mul_of_nonneg_right (coefficientMap_first_oneY hR u) hA.le).trans_eq (by ring))
  constructor
  · exact hb.trans ((mul_le_mul_of_nonneg_right (coefficientMap_second_oneY hR u) hA.le).trans_eq (by ring))
  · exact hb.trans ((mul_le_mul_of_nonneg_right (coefficientMap_third_oneY hR u) hA.le).trans_eq (by ring))

end
end Resonance.CubicParameterJets
