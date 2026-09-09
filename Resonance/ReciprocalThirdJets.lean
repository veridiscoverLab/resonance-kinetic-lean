import Resonance.SpatialChainRule
import Mathlib.Analysis.Calculus.IteratedDeriv.WithinZpow

/-! Ordered reciprocal jets used by the actual RJ coframe. Repeated spatial
directions are allowed; all three second-times-first parents are retained. -/
open Set
open scoped BigOperators ContDiff
namespace Resonance.ReciprocalThirdJets
noncomputable section
set_option maxHeartbeats 1500000

theorem scalar_inverse_iterated (n : ℕ) (x : ℝ) (v : Fin n→ℝ) :
    iteratedFDeriv ℝ n (fun y : ℝ => y⁻¹) x v=
      (∏ i,v i)*((-1:ℝ)^n*(n.factorial:ℝ)*x^(-1-(n:ℤ))) := by
  have h := iteratedDerivWithin_one_div (𝕜 := ℝ) n isOpen_univ (mem_univ x)
  rw [iteratedFDeriv_apply_eq_iteratedDeriv_mul_prod]
  simpa only [iteratedDerivWithin_univ,one_div,smul_eq_mul] using
    congrArg (fun z : ℝ => (∏ i,v i)*z) h

section Spatial
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def reciprocalJet (n : ℕ) (q : E→ℝ) (x : E) (v : Fin n→E) : ℝ :=
  iteratedFDeriv ℝ n (fun y => (q y)⁻¹) x v

def scaledJet (n : ℕ) (q : E→ℝ) (x : E) (v : Fin n→E) : ℝ :=
  (q x)⁻¹*iteratedFDeriv ℝ n q x v

def coframeB (n : ℕ) (q : E→ℝ) (x : E) (v : Fin n→E) : ℝ :=
  reciprocalJet n q x v/(q x)⁻¹+scaledJet n q x v

theorem reciprocal_first {q : E→ℝ} {x : E} (hq : q x≠0)
    (hf : ContDiffAt ℝ 1 q x) (a : E) :
    reciprocalJet 1 q x ![a]=-(q x)⁻¹^2*iteratedFDeriv ℝ 1 q x ![a] := by
  have h := (hasFDerivAt_inv hq).comp x (hf.differentiableAt (by norm_num)).hasFDerivAt
  simp only [Function.comp_def] at h
  unfold reciprocalJet
  rw [iteratedFDeriv_one_apply,h.fderiv]
  simp [iteratedFDeriv_one_apply,inv_pow,mul_comm]

theorem reciprocal_second {q : E→ℝ} {x : E} (hq : q x≠0)
    (hf : ContDiffAt ℝ 2 q x) (a b : E) :
    reciprocalJet 2 q x ![a,b]=
      2*(q x)⁻¹^3*(iteratedFDeriv ℝ 1 q x ![a])*(iteratedFDeriv ℝ 1 q x ![b])-
      (q x)⁻¹^2*iteratedFDeriv ℝ 2 q x ![a,b] := by
  have h := SpatialChainRule.composition_second (contDiffAt_inv ℝ hq) hf a b
  change reciprocalJet 2 q x ![a,b]=_ at h
  rw [h]
  simp only [scalar_inverse_iterated]
  norm_num [Fin.prod_univ_succ,zpow_neg,zpow_natCast,inv_pow]
  field_simp
  ring

theorem reciprocal_third {q : E→ℝ} {x : E} (hq : q x≠0)
    (hf : ContDiffAt ℝ 3 q x) (a b c : E) :
    reciprocalJet 3 q x ![a,b,c]=
      -6*(q x)⁻¹^4*(iteratedFDeriv ℝ 1 q x ![a])*(iteratedFDeriv ℝ 1 q x ![b])*
        (iteratedFDeriv ℝ 1 q x ![c])+
      2*(q x)⁻¹^3*((iteratedFDeriv ℝ 2 q x ![a,b])*(iteratedFDeriv ℝ 1 q x ![c])+
        (iteratedFDeriv ℝ 1 q x ![b])*(iteratedFDeriv ℝ 2 q x ![a,c])+
        (iteratedFDeriv ℝ 1 q x ![a])*(iteratedFDeriv ℝ 2 q x ![b,c]))-
      (q x)⁻¹^2*iteratedFDeriv ℝ 3 q x ![a,b,c] := by
  have h := SpatialChainRule.composition_third (contDiffAt_inv ℝ hq) hf a b c
  change reciprocalJet 3 q x ![a,b,c]=_ at h
  rw [h]
  simp only [scalar_inverse_iterated]
  norm_num [Fin.prod_univ_succ,zpow_neg,zpow_natCast,inv_pow]
  field_simp
  ring

theorem coframeB_zero {q : E→ℝ} {x : E} (hq : q x≠0) (v : Fin 0→E) :
    coframeB 0 q x v=2 := by
  norm_num [coframeB,reciprocalJet,scaledJet,iteratedFDeriv_zero_apply,hq]

theorem coframeB_first {q : E→ℝ} {x : E} (hq : q x≠0)
    (hf : ContDiffAt ℝ 1 q x) (a : E) : coframeB 1 q x ![a]=0 := by
  rw [coframeB,reciprocal_first hq hf]
  unfold scaledJet
  field_simp
  ring

theorem coframeB_second {q : E→ℝ} {x : E} (hq : q x≠0)
    (hf : ContDiffAt ℝ 2 q x) (a b : E) :
    coframeB 2 q x ![a,b]=2*scaledJet 1 q x ![a]*scaledJet 1 q x ![b] := by
  rw [coframeB,reciprocal_second hq hf]
  unfold scaledJet
  field_simp
  ring

theorem coframeB_third {q : E→ℝ} {x : E} (hq : q x≠0)
    (hf : ContDiffAt ℝ 3 q x) (a b c : E) :
    coframeB 3 q x ![a,b,c]=2*(scaledJet 1 q x ![a]*scaledJet 2 q x ![b,c]+
      scaledJet 1 q x ![b]*scaledJet 2 q x ![a,c]+
      scaledJet 1 q x ![c]*scaledJet 2 q x ![a,b])-
        6*scaledJet 1 q x ![a]*scaledJet 1 q x ![b]*scaledJet 1 q x ![c] := by
  rw [coframeB,reciprocal_third hq hf]
  unfold scaledJet
  field_simp
  ring

end Spatial
end
end Resonance.ReciprocalThirdJets

#check Resonance.ReciprocalThirdJets.scalar_inverse_iterated
#check Resonance.ReciprocalThirdJets.reciprocal_first
#check Resonance.ReciprocalThirdJets.reciprocal_second
#check Resonance.ReciprocalThirdJets.reciprocal_third
#check Resonance.ReciprocalThirdJets.coframeB_zero
#check Resonance.ReciprocalThirdJets.coframeB_first
#check Resonance.ReciprocalThirdJets.coframeB_second
#check Resonance.ReciprocalThirdJets.coframeB_third
#print axioms Resonance.ReciprocalThirdJets.scalar_inverse_iterated
#print axioms Resonance.ReciprocalThirdJets.reciprocal_first
#print axioms Resonance.ReciprocalThirdJets.reciprocal_second
#print axioms Resonance.ReciprocalThirdJets.reciprocal_third
#print axioms Resonance.ReciprocalThirdJets.coframeB_zero
#print axioms Resonance.ReciprocalThirdJets.coframeB_first
#print axioms Resonance.ReciprocalThirdJets.coframeB_second
#print axioms Resonance.ReciprocalThirdJets.coframeB_third
