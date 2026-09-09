import Resonance.ActualSobolevInclusion
import Resonance.ActualCoefficientSemigroup

/-! The full original normalized generator has order at most two. Its
uniform symbol bound follows from the proved original compact-parameter
matrix bounds; it is not an assumed generator bound. -/
namespace Resonance.ActualGeneratorOrder
noncomputable section
open Set Thermodynamics MatrixHilbertDictionary ActualComplexNormalization
open ActualUniformHilbertData ActualCompensatedDecay HilbertCompensatedGenerator
open ActualSobolevInclusion PhysicalFourierFrequencies PhysicalScalarFourier

theorem scalar_order_bound (r : ℝ) {c : ℝ} (hc : 0<c) :
    (1+r^2)⁻¹*r≤1 ∧ (1+r^2)⁻¹*(r^2/c)≤c⁻¹ := by
  have hp : 0<1+r^2 := by positivity
  constructor
  · have hn : r≤1+r^2 := by nlinarith [sq_nonneg (r-1)]
    simpa only [mul_assoc,inv_mul_cancel₀ hp.ne',mul_one] using
      mul_le_mul_of_nonneg_left hn (inv_nonneg.mpr hp.le)
  · have he : (1+r^2)⁻¹*(r^2/c)=((1+r^2)⁻¹*r^2)*c⁻¹ := by ring
    rw [he]
    apply mul_le_of_le_one_left (inv_nonneg.mpr hc.le)
    have hn : r^2≤1+r^2 := by linarith
    have hm := mul_le_mul_of_nonneg_left hn (inv_nonneg.mpr hp.le)
    simpa only [inv_mul_cancel₀ hp.ne'] using hm

theorem attenuated_generator_bound (A B : H→L[ℂ]H) {r c L : ℝ}
    (hr : 0≤r) (hc : 0<c) (hL : 0≤L) (hA : ‖A‖≤L) (hB : ‖B‖≤L) :
    ‖(((1+r^2)⁻¹:ℝ):ℂ) • generator A B r (r^2/c)‖≤L*(1+c⁻¹) := by
  have hnon : 0≤(1+r^2)⁻¹ := by positivity
  have hg : ‖generator A B r (r^2/c)‖≤r*L+(r^2/c)*L := by
    unfold generator
    push_cast
    calc
      _≤‖(-(r:ℂ)*Complex.I) • A‖+‖(r^2/c:ℂ) • B‖ := norm_sub_le _ _
      _=r*‖A‖+(r^2/c)*‖B‖ := by
        simp only [norm_smul,norm_mul,norm_neg,Complex.norm_I,mul_one,
          ←Complex.ofReal_pow,←Complex.ofReal_div,Complex.norm_real,Real.norm_eq_abs,
          abs_of_nonneg hr,abs_of_nonneg (by positivity : 0≤r^2/c)]
      _≤r*L+(r^2/c)*L := add_le_add
        (mul_le_mul_of_nonneg_left hA hr) (mul_le_mul_of_nonneg_left hB (by positivity))
  rw [norm_smul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hnon]
  calc
    _≤(1+r^2)⁻¹*(r*L+(r^2/c)*L) := mul_le_mul_of_nonneg_left hg hnon
    _=((1+r^2)⁻¹*r)*L+((1+r^2)⁻¹*(r^2/c))*L := by ring
    _≤1*L+c⁻¹*L := add_le_add
      (mul_le_mul_of_nonneg_right (scalar_order_bound r hc).1 hL)
      (mul_le_mul_of_nonneg_right (scalar_order_bound r hc).2 hL)
    _=L*(1+c⁻¹) := by ring

theorem original_generator_order {R : ℝ} (hR : 0<R) {θ : Parameter}
    (hθ : θ∈positiveDomain R) {c : ℝ} (hc : 0<c) :
    ∃D : ℝ,0≤D ∧ ∀n : Frequency,
      ‖smoothing n*modeGenerator hR hθ (direction n) c (radius n)‖≤D := by
  have hp : ({θ}:Set Parameter)⊆positiveDomain R := singleton_subset_iff.mpr hθ
  obtain ⟨β,k,L,_,_,hL,hdata⟩ := actual_uniform_hilbert_data hR isCompact_singleton hp
  refine ⟨L*(1+c⁻¹),by positivity,?_⟩
  intro n
  obtain ⟨hA,hB,_,_⟩ := hdata ⟨θ,mem_singleton θ⟩ (direction n)
  simpa only [smoothing,smul_mul_assoc,one_mul,attenuation,modeGenerator,
    FourierCompensationWeights.damping] using
    attenuated_generator_bound (A R θ (fun j=>(direction n).val j))
      (B hR hθ (fun j=>(direction n).val j)) (radius_nonneg n) hc hL.le hA hB

end
end Resonance.ActualGeneratorOrder
