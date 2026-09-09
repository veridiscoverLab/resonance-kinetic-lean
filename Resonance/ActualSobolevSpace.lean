import Resonance.PhysicalVectorFourier
import Resonance.PhysicalFourierFrequencies
import Resonance.ActualOriginalModeDecay

/-! Fourier construction of the original H^s,M completion, for every real s.
Stored coordinates are (1+|n|²)^(s/2) M^(1/2) v̂(n). The decoding map,
Gram norm identity, and dense finite Fourier approximations are proved.
In particular negative Sobolev orders are not asserted to lie in L². -/
open scoped ENNReal
namespace Resonance.ActualSobolevSpace
noncomputable section
open Thermodynamics MatrixHilbertDictionary ActualGramHilbert
open PhysicalScalarFourier PhysicalVectorFourier PhysicalFourierFrequencies
open L2DiagonalOperator ActualOriginalModeDecay

def weight (s : ℝ) (n : Frequency) : ℝ := (1+radius n^2)^(s/2)

theorem weight_positive (s : ℝ) (n : Frequency) : 0<weight s n :=
  Real.rpow_pos_of_pos (by positivity) _

theorem weight_square (s : ℝ) (n : Frequency) : weight s n^2=(1+radius n^2)^s := by
  rw [weight,←Real.rpow_mul_natCast (by positivity : 0≤1+radius n^2)]
  congr 1
  norm_num

abbrev Sobolev (_s : ℝ) := Space Frequency H

def coefficient {R : ℝ} (_hR : 0<R) {θ : Parameter} (_hθ : θ∈positiveDomain R)
    (s : ℝ) (v : Sobolev s) (n : Frequency) : H :=
  (((weight s n)⁻¹:ℝ):ℂ) • inverseOperator R θ (v n)

theorem root_coefficient {R : ℝ} (hR : 0<R) {θ : Parameter}
    (hθ : θ∈positiveDomain R) (s : ℝ) (v : Sobolev s) (n : Frequency) :
    rootOperator R θ (coefficient hR hθ s v n)=(((weight s n)⁻¹:ℝ):ℂ) • v n := by
  rw [coefficient,map_smul]
  have hi := DFunLike.congr_fun (original_root_inverse hR hθ) (v n)
  simpa only [ContinuousLinearMap.mul_apply,ContinuousLinearMap.one_apply] using
    congrArg (fun z:H=>(((weight s n)⁻¹:ℝ):ℂ) • z) hi

theorem coefficient_injective {R : ℝ} (hR : 0<R) {θ : Parameter}
    (hθ : θ∈positiveDomain R) (s : ℝ) :
    Function.Injective (coefficient hR hθ s) := by
  intro v w h
  apply Subtype.ext
  funext n
  have hh := congrArg (fun f:Frequency→H=>rootOperator R θ (f n)) h
  dsimp only at hh
  rw [root_coefficient,root_coefficient] at hh
  have hs := congrArg (fun z:H=>(weight s n:ℂ) • z) hh
  simpa only [smul_smul,←Complex.ofReal_mul,mul_inv_cancel₀ (weight_positive s n).ne',
    Complex.ofReal_one,one_smul] using hs

theorem weighted_gram_coefficient {R : ℝ} (hR : 0<R) {θ : Parameter}
    (hθ : θ∈positiveDomain R) (s : ℝ) (v : Sobolev s) (n : Frequency) :
    weight s n^2*gramEnergy R θ (coefficient hR hθ s v n)=‖v n‖^2 := by
  rw [gramEnergy,←original_gram_norm hR hθ,root_coefficient,norm_smul]
  have hw := weight_positive s n
  simp only [Complex.norm_real,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hw)]
  field_simp [hw.ne']

theorem sobolev_gram_parseval {R : ℝ} (hR : 0<R) {θ : Parameter}
    (hθ : θ∈positiveDomain R) (s : ℝ) (v : Sobolev s) :
    HasSum (fun n=>weight s n^2*gramEnergy R θ (coefficient hR hθ s v n)) (‖v‖^2) := by
  simpa only [weighted_gram_coefficient] using hasSum_norm_square v

def truncation (s : ℝ) (v : Sobolev s) (S : Finset Frequency) : Sobolev s :=
  ∑n∈S,lp.single 2 n (v n)

theorem finite_fourier_dense (s : ℝ) (v : Sobolev s) :
    Filter.Tendsto (truncation s v) Filter.atTop (nhds v) :=
  lp.hasSum_single (by norm_num : (2:ℝ≥0∞)≠∞) v

def finitePhysical {R : ℝ} (hR : 0<R) {θ : Parameter} (hθ : θ∈positiveDomain R)
    (s : ℝ) (v : Sobolev s) (S : Finset Frequency) : Field :=
  vectorFourier.symm (∑n∈S,lp.single 2 n (coefficient hR hθ s v n))

theorem finitePhysical_fourier {R : ℝ} (hR : 0<R) {θ : Parameter}
    (hθ : θ∈positiveDomain R) (s : ℝ) (v : Sobolev s)
    (S : Finset Frequency) (n : Frequency) :
    vectorFourier (finitePhysical hR hθ s v S) n=
      if n∈S then coefficient hR hθ s v n else 0 := by
  classical
  rw [finitePhysical,vectorFourier.apply_symm_apply]
  simp only [lp.coeFn_sum,Finset.sum_apply,lp.single_apply]
  simp

end
end Resonance.ActualSobolevSpace
