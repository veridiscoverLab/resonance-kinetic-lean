import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.InnerProductSpace.Dual

/-! Genuine product-kernel pairing and its operator-norm estimate. -/
open MeasureTheory Set
open scoped ENNReal InnerProductSpace
namespace Resonance.L2KernelPairing
noncomputable section
variable {X Y:Type*} [MeasurableSpace X] [MeasurableSpace Y]
variable (μ:Measure X) (ν:Measure Y) [SigmaFinite μ] [SigmaFinite ν]

omit [SigmaFinite μ] [SigmaFinite ν] in
theorem tensor_memLp (u:Lp ℝ 2 ν) (v:Lp ℝ 2 μ) :
    MemLp (fun p:X×Y=>v p.1*u p.2) 2 (μ.prod ν) := by
  apply (memLp_two_iff_integrable_sq
    ((Lp.aestronglyMeasurable v).comp_fst.mul (Lp.aestronglyMeasurable u).comp_snd)).mpr
  simpa only [Pi.mul_apply,mul_pow] using (Lp.memLp v).integrable_sq.mul_prod (Lp.memLp u).integrable_sq

def tensor (u:Lp ℝ 2 ν) (v:Lp ℝ 2 μ) : Lp ℝ 2 (μ.prod ν) :=
  (tensor_memLp μ ν u v).toLp _

omit [SigmaFinite μ] [SigmaFinite ν] in
theorem tensor_coe (u:Lp ℝ 2 ν) (v:Lp ℝ 2 μ) :
    tensor μ ν u v=ᵐ[μ.prod ν](fun p:X×Y=>v p.1*u p.2) := MemLp.coeFn_toLp _

omit [SigmaFinite μ] in
theorem norm_sq_integral (u:Lp ℝ 2 μ) : ‖u‖^2=∫x,(u x)^2 ∂μ := by
  rw [← real_inner_self_eq_norm_sq,L2.inner_def]
  congr 1
  ext x
  simp [pow_two]

theorem tensor_norm_sq (u:Lp ℝ 2 ν) (v:Lp ℝ 2 μ) :
    ‖tensor μ ν u v‖^2=‖v‖^2*‖u‖^2 := by
  rw [norm_sq_integral]
  calc
    (∫p,(tensor μ ν u v p)^2 ∂(μ.prod ν))
        =∫p,(v p.1)^2*(u p.2)^2 ∂(μ.prod ν) :=
      integral_congr_ae ((tensor_coe μ ν u v).mono (fun p h=>by
        change (tensor μ ν u v p)^2=(v p.1)^2*(u p.2)^2
        rw [h,mul_pow]))
    _ = (∫x,(v x)^2 ∂μ)*(∫y,(u y)^2 ∂ν) :=
      integral_prod_mul (μ:=μ) (ν:=ν) (fun x=>(v x)^2) (fun y=>(u y)^2)
    _ = ‖v‖^2*‖u‖^2 := by rw [←norm_sq_integral,←norm_sq_integral]

theorem tensor_norm (u:Lp ℝ 2 ν) (v:Lp ℝ 2 μ) :
    ‖tensor μ ν u v‖=‖v‖*‖u‖ := by
  have h:=tensor_norm_sq μ ν u v
  nlinarith [norm_nonneg (tensor μ ν u v),mul_nonneg (norm_nonneg v) (norm_nonneg u)]

omit [SigmaFinite μ] [SigmaFinite ν] in
theorem pairing_integrable (K:Lp ℝ 2 (μ.prod ν)) (u:Lp ℝ 2 ν) (v:Lp ℝ 2 μ) :
    Integrable (fun p=>K p*u p.2*v p.1) (μ.prod ν) := by
  apply ((Lp.memLp K).integrable_mul (tensor_memLp μ ν u v)).congr
  filter_upwards with p
  simp only [Pi.mul_apply]
  ring

omit [SigmaFinite μ] [SigmaFinite ν] in
theorem pairing_eq_inner (K:Lp ℝ 2 (μ.prod ν)) (u:Lp ℝ 2 ν) (v:Lp ℝ 2 μ) :
    (∫p,K p*u p.2*v p.1 ∂(μ.prod ν))=inner ℝ K (tensor μ ν u v) := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [tensor_coe μ ν u v] with p hp
  simp only [hp]
  change K p*u p.2*v p.1=(v p.1*u p.2)*K p
  ring

theorem pairing_bound (K:Lp ℝ 2 (μ.prod ν)) (u:Lp ℝ 2 ν) (v:Lp ℝ 2 μ) :
    |∫p,K p*u p.2*v p.1 ∂(μ.prod ν)|≤‖K‖*‖u‖*‖v‖ := by
  rw [pairing_eq_inner]
  calc
    |inner ℝ K (tensor μ ν u v)|≤‖K‖*‖tensor μ ν u v‖ := abs_real_inner_le_norm _ _
    _ = ‖K‖*‖u‖*‖v‖ := by rw [tensor_norm]; ring

def Represents (K:Lp ℝ 2 (μ.prod ν)) (T:Lp ℝ 2 ν→L[ℝ]Lp ℝ 2 μ) : Prop :=
  ∀u v,inner ℝ v (T u)=∫p,K p*u p.2*v p.1 ∂(μ.prod ν)

theorem represents_norm_bound {K:Lp ℝ 2 (μ.prod ν)} {T:Lp ℝ 2 ν→L[ℝ]Lp ℝ 2 μ}
    (h:Represents μ ν K T) : ‖T‖≤‖K‖ := by
  apply ContinuousLinearMap.opNorm_le_bound T (norm_nonneg K)
  intro u
  have hb:=pairing_bound μ ν K u (T u)
  rw [←h, real_inner_self_eq_norm_sq] at hb
  rw [abs_of_nonneg (sq_nonneg _)] at hb
  by_cases ht:T u=0
  · simp [ht,mul_nonneg (norm_nonneg K) (norm_nonneg u)]
  · exact (mul_le_mul_iff_right₀ (norm_pos_iff.mpr ht)).mp (by nlinarith [hb])

omit [SigmaFinite μ] [SigmaFinite ν] in
theorem represents_iff_inner (K:Lp ℝ 2 (μ.prod ν)) (T:Lp ℝ 2 ν→L[ℝ]Lp ℝ 2 μ) :
    Represents μ ν K T ↔ ∀u v,inner ℝ v (T u)=inner ℝ K (tensor μ ν u v) := by
  simp only [Represents,pairing_eq_inner]

omit [SigmaFinite μ] [SigmaFinite ν] in
theorem represents_zero : Represents μ ν 0 0 := by
  rw [represents_iff_inner]
  simp

omit [SigmaFinite μ] [SigmaFinite ν] in
theorem Represents.add {K L:Lp ℝ 2 (μ.prod ν)} {T S:Lp ℝ 2 ν→L[ℝ]Lp ℝ 2 μ}
    (hT:Represents μ ν K T) (hS:Represents μ ν L S) : Represents μ ν (K+L) (T+S) := by
  rw [represents_iff_inner] at hT hS ⊢
  intro u v
  simp only [ContinuousLinearMap.add_apply,inner_add_right,inner_add_left,hT,hS]

omit [SigmaFinite μ] [SigmaFinite ν] in
theorem Represents.smul {K:Lp ℝ 2 (μ.prod ν)} {T:Lp ℝ 2 ν→L[ℝ]Lp ℝ 2 μ}
    (hT:Represents μ ν K T) (a:ℝ) : Represents μ ν (a•K) (a•T) := by
  rw [represents_iff_inner] at hT ⊢
  intro u v
  simp only [ContinuousLinearMap.smul_apply,real_inner_smul_left,real_inner_smul_right,hT]

omit [SigmaFinite μ] [SigmaFinite ν] in
theorem Represents.sub {K L:Lp ℝ 2 (μ.prod ν)} {T S:Lp ℝ 2 ν→L[ℝ]Lp ℝ 2 μ}
    (hT:Represents μ ν K T) (hS:Represents μ ν L S) : Represents μ ν (K-L) (T-S) := by
  rw [represents_iff_inner] at hT hS ⊢
  intro u v
  simp only [ContinuousLinearMap.sub_apply,inner_sub_right,inner_sub_left,hT,hS]

theorem tensor_inner (a v:Lp ℝ 2 μ) (b u:Lp ℝ 2 ν) :
    inner ℝ (tensor μ ν b a) (tensor μ ν u v)=inner ℝ a v*inner ℝ b u := by
  rw [L2.inner_def]
  calc
    (∫p,inner ℝ (tensor μ ν b a p) (tensor μ ν u v p) ∂(μ.prod ν))
        =∫p,(inner ℝ (a p.1) (v p.1))*(inner ℝ (b p.2) (u p.2)) ∂(μ.prod ν) := by
      apply integral_congr_ae
      filter_upwards [tensor_coe μ ν b a,tensor_coe μ ν u v] with p hp hq
      rw [hp,hq]
      change (v p.1*u p.2)*(a p.1*b p.2)=(v p.1*a p.1)*(u p.2*b p.2)
      ring
    _ = (∫x,inner ℝ (a x) (v x) ∂μ)*(∫y,inner ℝ (b y) (u y) ∂ν) :=
      integral_prod_mul (μ:=μ) (ν:=ν) (fun x=>inner ℝ (a x) (v x)) (fun y=>inner ℝ (b y) (u y))
    _ = inner ℝ a v*inner ℝ b u := by rw [L2.inner_def,L2.inner_def]

end
end Resonance.L2KernelPairing
