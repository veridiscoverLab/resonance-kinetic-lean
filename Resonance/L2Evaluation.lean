import Resonance.L2DiagonalOperator
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-! Genuine bounded coordinate evaluations on the completed joint L²
coefficient space, including their Bochner interval-integral identity. -/
namespace Resonance.L2Evaluation
noncomputable section
open L2DiagonalOperator MeasureTheory
variable {I E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

def evaluation (i : I) : Space I E→L[ℂ]E where
  toFun v:=v i
  map_add' _ _:=rfl
  map_smul' _ _:=rfl
  cont:=(continuous_apply i).comp lp.uniformContinuous_coe.continuous

theorem evaluation_apply (i : I) (v : Space I E) : evaluation i v=v i := rfl

set_option backward.isDefEq.respectTransparency false in
theorem evaluation_intervalIntegral [CompleteSpace E] (i : I) {f : ℝ→Space I E}
    {a b : ℝ} (hf : IntervalIntegrable f volume a b) :
    (∫t in a..b,f t) i=∫t in a..b,f t i :=
  ((evaluation i).intervalIntegral_comp_comm hf).symm

end
end Resonance.L2Evaluation
