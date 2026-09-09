import Resonance.PinnedClosedForm

/-! The paper's positive γ/4 normalization is implemented on the same
maximal domain by scaling the actual full-difference operator. -/
open Real Set MeasureTheory Filter
open scoped Topology ENNReal ComplexConjugate
namespace Resonance.PinnedScaledDifference
noncomputable section
open Resonance.PinnedMaximalDifference Resonance.PinnedSmoothDomain
open Resonance.PinnedClosedForm

def factor (γ : ℝ) : ℂ := (Real.sqrt (γ/4):ℝ)
def scaledDifference {d : ℝ} (hd0 : 0<d) (hdU : d<1/2)
    (a : FourCircle→ℝ) (γ : ℝ) : Source →ₗ.[ℂ] Target d a :=
  factor γ • maximalDifference hd0 hdU a

theorem factor_ne_zero {γ : ℝ} (hγ : 0<γ) : factor γ≠0 := by
  unfold factor
  exact_mod_cast (Real.sqrt_pos.mpr (div_pos hγ (show (0:ℝ)<4 by norm_num))).ne'

theorem scaledDifference_domain {d : ℝ} (hd0 : 0<d) (hdU : d<1/2)
    (a : FourCircle→ℝ) (γ : ℝ) :
    (scaledDifference hd0 hdU a γ).domain=(maximalDifference hd0 hdU a).domain := rfl

theorem scaledDifference_apply {d : ℝ} (hd0 : 0<d) (hdU : d<1/2)
    (a : FourCircle→ℝ) (γ : ℝ) (u : FormDomain hd0 hdU a) :
    scaledDifference hd0 hdU a γ u=factor γ • maximalDifference hd0 hdU a u := rfl

theorem scaledDifference_graph {d : ℝ} (hd0 : 0<d) (hdU : d<1/2)
    (a : FourCircle→ℝ) {γ : ℝ} (hγ : 0<γ) :
    ((scaledDifference hd0 hdU a γ).graph : Set (Source × Target d a))=
      (fun p : Source × Target d a => (p.1,(factor γ)⁻¹ • p.2)) ⁻¹'
        ((maximalDifference hd0 hdU a).graph : Set (Source × Target d a)) := by
  apply Set.ext
  intro p
  change p∈(scaledDifference hd0 hdU a γ).graph ↔
    (p.1,(factor γ)⁻¹ • p.2)∈(maximalDifference hd0 hdU a).graph
  rw [LinearPMap.mem_graph_iff,LinearPMap.mem_graph_iff]
  constructor
  · rintro ⟨u,hu,hv⟩
    refine ⟨u,hu,?_⟩
    rw [← hv,scaledDifference_apply,inv_smul_smul₀ (factor_ne_zero hγ)]
  · rintro ⟨u,hu,hv⟩
    refine ⟨u,hu,?_⟩
    rw [scaledDifference_apply,hv,smul_inv_smul₀ (factor_ne_zero hγ)]

theorem scaledDifference_isClosed {d : ℝ} (hd0 : 0<d) (hdU : d<1/2)
    (a : FourCircle→ℝ) {γ : ℝ} (hγ : 0<γ) :
    (scaledDifference hd0 hdU a γ).IsClosed := by
  rw [LinearPMap.IsClosed,scaledDifference_graph hd0 hdU a hγ]
  exact (maximalDifference_isClosed hd0 hdU a).preimage
    (continuous_fst.prodMk (continuous_const.smul continuous_snd))

theorem scaledDifference_dense_domain {d : ℝ} (hd0 : 0<d) (hdU : d<1/2)
    {a : FourCircle→ℝ} (ha : Continuous a) (γ : ℝ) :
    Dense ((scaledDifference hd0 hdU a γ).domain : Set Source) :=
  maximalDifference_dense_domain hd0 hdU ha

theorem scaled_inner_eq_form {d : ℝ} (hd0 : 0<d) (hdU : d<1/2)
    (a : FourCircle→ℝ) {γ : ℝ} (hγ : 0≤γ) (u v : FormDomain hd0 hdU a) :
    inner ℂ (scaledDifference hd0 hdU a γ u) (scaledDifference hd0 hdU a γ v)=
      form hd0 hdU a γ u v := by
  rw [scaledDifference_apply,scaledDifference_apply,inner_smul_left,inner_smul_right]
  have hsq : (factor γ)*(factor γ)=(γ/4:ℂ) := by
    dsimp [factor]
    norm_cast
    nlinarith [Real.sq_sqrt (div_nonneg hγ (show (0:ℝ)≤4 by norm_num))]
  have hstar : star (factor γ)=factor γ := by simp [factor]
  change star (factor γ)*(factor γ*_)=(γ/4:ℂ)*_
  rw [hstar,←mul_assoc,hsq]

end
end Resonance.PinnedScaledDifference
