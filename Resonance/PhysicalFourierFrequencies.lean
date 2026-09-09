import Resonance.PhysicalScalarFourier
import Resonance.ActualUniformHilbertData

/-! The true integer frequencies for the original 2π torus, including
zero and every direction. The lower bound away from zero is proved from
the integer lattice, not imposed as a spectral assumption. -/
open Set
namespace Resonance.PhysicalFourierFrequencies
noncomputable section
open PhysicalScalarFourier ActualUniformHilbertData

def realFrequency (n : Frequency) : W := WithLp.toLp 2 (fun j=>(n j:ℝ))
def radius (n : Frequency) : ℝ := ‖realFrequency n‖

theorem realFrequency_zero_iff (n : Frequency) : realFrequency n=0 ↔ n=0 := by
  constructor
  · intro h
    funext j
    have hh := congrArg (fun x:W=>x j) h
    change (n j:ℝ)=0 at hh
    exact_mod_cast hh
  · rintro rfl
    ext j
    simp [realFrequency]

theorem radius_nonneg (n : Frequency) : 0≤radius n := norm_nonneg _
theorem radius_zero : radius 0=0 := by
  rw [radius,(realFrequency_zero_iff 0).mpr rfl,norm_zero]

theorem radius_lower {n : Frequency} (hn : n≠0) : 1≤radius n := by
  have hex : ∃j,n j≠0 := by
    by_contra hh
    push Not at hh
    exact hn (funext hh)
  obtain ⟨j,hj⟩ := hex
  have hInt : (1:ℤ)≤|n j| := by
    have hp : (0:ℤ) < |n j| := abs_pos.mpr hj
    omega
  have hh : (1:ℝ)≤|(n j:ℝ)| := by exact_mod_cast hInt
  exact hh.trans (by simpa only [realFrequency,Real.norm_eq_abs] using
    PiLp.norm_apply_le (realFrequency n) j)

def fixedDirection : UnitDirection := ⟨WithLp.toLp 2 ![(1:ℝ),0,0],by
  rw [Metric.mem_sphere,dist_zero_right]
  have hs := PiLp.norm_sq_eq_of_L2 (fun _:Fin 3=>ℝ) (WithLp.toLp 2 ![(1:ℝ),0,0])
  norm_num [Fin.sum_univ_succ] at hs
  rcases hs with hs|hs
  · exact hs
  · exfalso
    linarith [norm_nonneg (WithLp.toLp 2 ![(1:ℝ),0,0])]
⟩

def direction (n : Frequency) : UnitDirection := if hn:realFrequency n=0 then fixedDirection else
  ⟨(radius n)⁻¹ • realFrequency n,by
    rw [Metric.mem_sphere,dist_zero_right,norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr (radius_nonneg n))]
    exact inv_mul_cancel₀ (norm_ne_zero_iff.mpr hn)⟩

theorem radial_coordinates (n : Frequency) :
    radius n • (fun j=>(direction n).val j)=(fun j=>(n j:ℝ)) := by
  by_cases hn:realFrequency n=0
  · have hz := (realFrequency_zero_iff n).mp hn
    subst n
    funext j
    simp only [radius_zero,zero_smul,Pi.zero_apply,Int.cast_zero]
  · have hr : radius n≠0 := norm_ne_zero_iff.mpr hn
    funext j
    simp only [direction,dif_neg hn]
    change radius n*((radius n)⁻¹*(n j:ℝ))=(n j:ℝ)
    rw [←mul_assoc,mul_inv_cancel₀ hr,one_mul]

end
end Resonance.PhysicalFourierFrequencies
