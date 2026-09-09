import Resonance.ActualSobolevInclusion
import Resonance.PhysicalFourierDerivatives

/-! The actual first and mixed second spatial derivatives as bounded maps
H^s to H^(s-2). Their symbols are those proved for the original trigonometric
characters, with all five physical components kept together. -/
namespace Resonance.ActualSpatialDifferentials
noncomputable section
open Thermodynamics MatrixHilbertDictionary ActualGramHilbert ActualSobolevSpace
open ActualSobolevInclusion PhysicalScalarFourier PhysicalFourierFrequencies L2DiagonalOperator

theorem coordinate_bound (n : Frequency) (j : Fin 3) : |(n j:ℝ)|≤radius n := by
  simpa only [Real.norm_eq_abs] using (PiLp.norm_apply_le (realFrequency n) j)

theorem attenuation_coordinate_bound (n : Frequency) (j : Fin 3) :
    attenuation n*|(n j:ℝ)|≤1 := by
  calc
    _≤attenuation n*radius n := mul_le_mul_of_nonneg_left (coordinate_bound n j)
      (attenuation_positive n).le
    _≤1 := by
      have hp : 0<1+radius n^2 := by positivity
      have hn : radius n≤1+radius n^2 := by nlinarith [sq_nonneg (radius n-1)]
      simpa only [attenuation,inv_mul_cancel₀ hp.ne'] using
        mul_le_mul_of_nonneg_left hn (inv_nonneg.mpr hp.le)

theorem attenuation_product_bound (n : Frequency) (i j : Fin 3) :
    attenuation n*(|(n i:ℝ)| * |(n j:ℝ)|)≤1 := by
  have hm : |(n i:ℝ)| * |(n j:ℝ)|≤radius n^2 := by
    simpa only [pow_two] using mul_le_mul (coordinate_bound n i) (coordinate_bound n j)
      (abs_nonneg _) (radius_nonneg n)
  calc
    _≤attenuation n*radius n^2 := mul_le_mul_of_nonneg_left hm (attenuation_positive n).le
    _≤1 := by
      have hp : 0<1+radius n^2 := by positivity
      have hn : radius n^2≤1+radius n^2 := by linarith
      simpa only [attenuation,inv_mul_cancel₀ hp.ne'] using
        mul_le_mul_of_nonneg_left hn (inv_nonneg.mpr hp.le)

def firstSymbol (n : Frequency) (j : Fin 3) : ℂ := Complex.I*(n j:ℂ)
def secondSymbol (n : Frequency) (i j : Fin 3) : ℂ := -((n i:ℂ)*(n j:ℂ))

def multiplierLeg (m : Frequency→ℂ) (n : Frequency) : H→L[ℂ]H :=
  ((attenuation n:ℂ)*m n) • (1:H→L[ℂ]H)

theorem first_leg_bound (j : Fin 3) (n : Frequency) :
    ‖multiplierLeg (fun n=>firstSymbol n j) n‖≤1 := by
  simpa only [multiplierLeg,firstSymbol,norm_smul,norm_mul,norm_one,mul_one,
    Complex.norm_I,one_mul,Complex.norm_real,Real.norm_eq_abs,Complex.norm_intCast,
    ←Int.cast_abs,abs_of_pos (attenuation_positive n)] using attenuation_coordinate_bound n j

theorem second_leg_bound (i j : Fin 3) (n : Frequency) :
    ‖multiplierLeg (fun n=>secondSymbol n i j) n‖≤1 := by
  simpa only [multiplierLeg,secondSymbol,norm_smul,norm_mul,norm_one,mul_one,norm_neg,
    Complex.norm_real,Real.norm_eq_abs,Complex.norm_intCast,←Int.cast_abs,
    abs_of_pos (attenuation_positive n)] using attenuation_product_bound n i j

def first (s : ℝ) (j : Fin 3) : Sobolev s→L[ℂ]Sobolev (s-2) :=
  diagonal (multiplierLeg (fun n=>firstSymbol n j)) (by norm_num) (first_leg_bound j)

def second (s : ℝ) (i j : Fin 3) : Sobolev s→L[ℂ]Sobolev (s-2) :=
  diagonal (multiplierLeg (fun n=>secondSymbol n i j)) (by norm_num) (second_leg_bound i j)

theorem multiplier_coefficient {R : ℝ} (hR : 0<R) {θ : Parameter}
    (hθ : θ∈positiveDomain R) (s : ℝ) (m : Frequency→ℂ) {C : ℝ}
    (hC : 0≤C) (hm : ∀n,‖multiplierLeg m n‖≤C) (v : Sobolev s) (n : Frequency) :
    coefficient hR hθ (s-2) (diagonal (multiplierLeg m) hC hm v) n=
      m n • coefficient hR hθ s v n := by
  change (((weight (s-2) n)⁻¹:ℝ):ℂ) •
    inverseOperator R θ (((attenuation n:ℂ)*m n) • v n)=_
  simp only [map_smul,coefficient,smul_smul]
  rw [weight_shift]
  have he : (attenuation n*weight s n)⁻¹*attenuation n=(weight s n)⁻¹ := by
    field_simp [(attenuation_positive n).ne',(weight_positive s n).ne']
  rw [←mul_assoc,←Complex.ofReal_mul,he,mul_comm]

theorem first_coefficient {R : ℝ} (hR : 0<R) {θ : Parameter}
    (hθ : θ∈positiveDomain R) (s : ℝ) (j : Fin 3) (v : Sobolev s) (n : Frequency) :
    coefficient hR hθ (s-2) (first s j v) n=
      firstSymbol n j • coefficient hR hθ s v n := multiplier_coefficient hR hθ s _ _ _ v n

theorem second_coefficient {R : ℝ} (hR : 0<R) {θ : Parameter}
    (hθ : θ∈positiveDomain R) (s : ℝ) (i j : Fin 3) (v : Sobolev s) (n : Frequency) :
    coefficient hR hθ (s-2) (second s i j v) n=
      secondSymbol n i j • coefficient hR hθ s v n := multiplier_coefficient hR hθ s _ _ _ v n

end
end Resonance.ActualSpatialDifferentials
