import Resonance.HilbertODEEnergy

/-! Uniform Fourier ODE decay with the original rate c r²/(c²+r²).
The coercivity and coupling hypotheses refer to the very same A, B, and e;
the actual kinetic matrices are instantiated separately. -/
open ContinuousLinearMap InnerProductSpace
namespace Resonance.FourierODEDecay
noncomputable section
open RankTwoHilbert HilbertQuadraticBounds HilbertCompensatedGenerator
open FourierCompensationWeights UniformHilbertCompensation HilbertODEEnergy
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E]

theorem fourier_ODE_decay (A B : E→L[ℂ]E) (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B)
    {e : E} (he : ‖e‖=1) (hBe : B e=0) {β k L : ℝ} (hβ : 0<β) (hk : 0<k)
    (hcoupling : k≤‖coupling A e‖^2)
    (hcoerc : ∀v:E,β*‖micro e v‖^2≤quadratic B v)
    (hAnorm : ‖A‖≤L) (hBnorm : ‖B‖≤L)
    {c r : ℝ} (hc : 0<c) (hr : 0≤r)
    {u : ℝ→E} (hu : ∀s,HasDerivAt u (generator A B r (damping c r) (u s)) s)
    {t : ℝ} (ht : 0≤t) :
    ‖u t‖^2≤3*Real.exp (-(2*decayBudget β k L/3)*rate c r*t)*‖u 0‖^2 := by
  have hL : 0≤L := (norm_nonneg A).trans hAnorm
  have hδ : 0≤decayBudget β k L*rate c r :=
    mul_nonneg (decayBudget_positive hβ hk hL).le
      (weight_nonnegative (by positivity : (0:ℝ)≤1) hc hr).1
  have hb := uniform_compensation A B hA hB he hBe hβ hk hcoupling hcoerc hAnorm hBnorm hc hr
  have hd := quadratic_ODE_decay (energyMetric A e β k L c r)
    (generator A B r (damping c r)) hδ (fun v=>(hb v).1)
    (fun v=>(hb v).2.1) (fun v=>by simpa only [neg_mul] using (hb v).2.2) hu ht
  have heq : -(2*(decayBudget β k L*rate c r)/3)*t=
      -(2*decayBudget β k L/3)*rate c r*t := by ring
  simpa only [heq] using hd

end
end Resonance.FourierODEDecay
