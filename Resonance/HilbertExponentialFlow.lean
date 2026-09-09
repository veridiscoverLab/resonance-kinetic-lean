import Resonance.FourierODEDecay
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.Complex.RealDeriv

/-! The actual operator exponential and its trajectory derivative, rather
than a postulated solution family. -/
open ContinuousLinearMap InnerProductSpace
namespace Resonance.HilbertExponentialFlow
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

def flow (G : E→L[ℂ]E) (t : ℝ) : E→L[ℂ]E := NormedSpace.exp ((t:ℂ) • G)

omit [CompleteSpace E] in
theorem flow_zero (G : E→L[ℂ]E) : flow G 0=1 := by
  simp [flow,NormedSpace.exp_zero]

theorem flow_add (G : E→L[ℂ]E) (s t : ℝ) :
    flow G (s+t)=flow G s*flow G t := by
  unfold flow
  rw [Complex.ofReal_add,add_smul]
  exact NormedSpace.exp_add_of_commute_of_mem_ball
    ((Commute.refl G).smul_left (s:ℂ) |>.smul_right (t:ℂ))
    ((NormedSpace.expSeries_radius_eq_top ℂ (E→L[ℂ]E)).symm ▸ edist_lt_top _ _)
    ((NormedSpace.expSeries_radius_eq_top ℂ (E→L[ℂ]E)).symm ▸ edist_lt_top _ _)

set_option backward.isDefEq.respectTransparency false in
theorem flow_hasDerivAt (G : E→L[ℂ]E) (v : E) (t : ℝ) :
    HasDerivAt (fun s=>flow G s v) (G (flow G t v)) t := by
  have h := hasDerivAt_exp_smul_const' G (t:ℂ)
  let he := ContinuousLinearMap.apply ℂ E v
  have hh := (he.hasFDerivAt.comp_hasDerivAt (t:ℂ) h).hasFDerivAt.restrictScalars ℝ
  convert hh.comp_hasDerivAt t Complex.ofRealCLM.hasDerivAt using 1
  change G (flow G t v)= (1:ℂ) • G (flow G t v)
  rw [one_smul]

end
end Resonance.HilbertExponentialFlow
