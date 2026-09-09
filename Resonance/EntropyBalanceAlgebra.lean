import Resonance.PhaseRelativeEntropy

/-! Assembly of the exact entropy balance. The analytic cancellation
hypotheses in this purely algebraic lemma are discharged on the actual
mild solution in ActualMicroscopicEntropy. -/
namespace Resonance.EntropyBalanceAlgebra
noncomputable section
open FreeTransport PhaseEnergy

theorem assemble (R c D : ℝ) (f q C A B dq : Distribution R)
    (ht : integralCLM R ((f-Ring.inverse q)*dq)=0)
    (hc : integralCLM R (C*q)=0)
    (hd : integralCLM R (C*Ring.inverse f)=D)
    (ha : integralCLM R (A*Ring.inverse f)=0)
    (hab : integralCLM R (A*q) = -integralCLM R (f*B))
    (hb : integralCLM R (Ring.inverse q*B)=0) :
    integralCLM R ((c • C-A)*(q-Ring.inverse f)+(f-Ring.inverse q)*dq)=
      -c*D+integralCLM R ((f-Ring.inverse q)*B) := by
  rw [map_add,ht,add_zero]
  simp only [sub_mul,mul_sub,smul_mul_assoc,map_sub,map_smul,smul_eq_mul]
  rw [hc,hd,ha,hab,hb]
  ring

end
end Resonance.EntropyBalanceAlgebra
