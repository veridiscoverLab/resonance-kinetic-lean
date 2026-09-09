import Resonance.ActualSobolevSpace
import Resonance.L2DiagonalOperator

/-! The actual two-derivative Sobolev inclusion. It preserves every decoded
physical Fourier coefficient, rather than identifying differently weighted
copies of the coefficient space by their common underlying type. -/
namespace Resonance.ActualSobolevInclusion
noncomputable section
open Thermodynamics MatrixHilbertDictionary ActualSobolevSpace
open PhysicalScalarFourier PhysicalFourierFrequencies L2DiagonalOperator

def attenuation (n : Frequency) : ℝ := (1+radius n^2)⁻¹

theorem attenuation_positive (n : Frequency) : 0<attenuation n := by
  unfold attenuation
  positivity

theorem attenuation_le_one (n : Frequency) : attenuation n≤1 := by
  rw [attenuation,inv_le_one₀ (by positivity)]
  nlinarith [sq_nonneg (radius n)]

theorem weight_shift (s : ℝ) (n : Frequency) :
    weight (s-2) n=attenuation n*weight s n := by
  have hb : 0<1+radius n^2 := by positivity
  have he : (s-2)/2=(-1:ℝ)+s/2 := by ring
  rw [weight,he,Real.rpow_add hb,Real.rpow_neg_one]
  rfl

def smoothing (n : Frequency) : H→L[ℂ]H :=
  (attenuation n:ℂ) • (1:H→L[ℂ]H)

theorem smoothing_norm (n : Frequency) : ‖smoothing n‖≤1 := by
  rw [smoothing,norm_smul,Complex.norm_real,Real.norm_eq_abs,
    abs_of_pos (attenuation_positive n)]
  simpa only [norm_one,mul_one] using attenuation_le_one n

def inclusion (s : ℝ) : Sobolev s→L[ℂ]Sobolev (s-2) :=
  diagonal smoothing (by norm_num : (0:ℝ)≤1) smoothing_norm

theorem inclusion_apply (s : ℝ) (v : Sobolev s) (n : Frequency) :
    inclusion s v n=(attenuation n:ℂ) • v n := rfl

theorem inclusion_norm (s : ℝ) : ‖inclusion s‖≤1 :=
  diagonal_norm _ _ _

theorem inclusion_coefficient {R : ℝ} (hR : 0<R) {θ : Parameter}
    (hθ : θ∈positiveDomain R) (s : ℝ) (v : Sobolev s) (n : Frequency) :
    coefficient hR hθ (s-2) (inclusion s v) n=coefficient hR hθ s v n := by
  simp only [coefficient,inclusion_apply,map_smul,smul_smul,←Complex.ofReal_mul]
  rw [weight_shift]
  have ha := (attenuation_positive n).ne'
  have hw := (weight_positive s n).ne'
  congr 2
  field_simp

end
end Resonance.ActualSobolevInclusion
