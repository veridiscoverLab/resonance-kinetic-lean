import Resonance.ActualNormalizedCoupling

/-! Continuous actual normalized mass and coupling vectors. -/
namespace Resonance.ActualNormalizedContinuity
noncomputable section
open Thermodynamics ActualGramRoot ActualNormalizedMatrices ActualFourierRank
open GramCoefficientContinuity ActualMassNormalization ActualNormalizedCoupling

theorem original_mass_square_continuous (R : ℝ) :
    Continuous (fun θ : positiveDomain R=>massSquare R θ) := by
  have hm : Continuous (fun θ : positiveDomain R=>gramMatrix R θ) :=
    continuousOn_iff_continuous_restrict.mp (original_gram_continuousOn R)
  exact quadratic_continuous.comp (hm.prodMk (continuous_const (y := massDirection)))

theorem original_mass_length_continuous (R : ℝ) :
    Continuous (fun θ : positiveDomain R=>massLength R θ) :=
  Real.continuous_sqrt.comp (original_mass_square_continuous R)

theorem original_mass_vector_continuous {R : ℝ} (hR : 0 < R) :
    Continuous (fun θ : positiveDomain R=>massVector R θ) := by
  have hl := (original_mass_length_continuous R).inv₀
    (fun θ=>(original_mass_length_positive hR θ.property).ne')
  exact hl.smul ((original_root_continuous hR).matrix_mulVec continuous_const)

theorem original_coupling_continuous {R : ℝ} (hR : 0 < R) :
    Continuous (fun p : positiveDomain R×(Fin 3→ℝ)=>actualCoupling R p.1 p.2) := by
  have he : Continuous (fun p : positiveDomain R×(Fin 3→ℝ)=>massVector R p.1) :=
    (original_mass_vector_continuous hR).comp continuous_fst
  have ha := (original_normalized_euler_continuous hR).matrix_mulVec he
  exact ha.sub ((he.dotProduct ha).smul he)

end
end Resonance.ActualNormalizedContinuity
