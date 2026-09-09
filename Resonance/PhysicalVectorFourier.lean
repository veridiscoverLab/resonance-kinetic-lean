import Resonance.PhysicalScalarFourier
import Resonance.L2DiagonalOperator
import Resonance.MatrixHilbertDictionary

/-! The full five-component Fourier isometry on the original spatial
torus. The finite component sum and infinite frequency sum are exchanged
only after the actual scalar Parseval summability has been established. -/
open ContinuousLinearMap
open scoped ENNReal
namespace Resonance.PhysicalVectorFourier
noncomputable section
open PhysicalScalarFourier MatrixHilbertDictionary L2DiagonalOperator
abbrev Field := PiLp 2 (fun _:Fin 5=>PhysicalScalar)
abbrev Coefficients := Space Frequency H

def coefficients (f : Field) (n : Frequency) : H :=
  WithLp.toLp 2 (fun j=>fourierIsometry (f j) n)

theorem coefficients_hasSum (f : Field) :
    HasSum (fun n=>‖coefficients f n‖^2) (‖f‖^2) := by
  have hh := hasSum_sum (s:=Finset.univ) (fun j _=>physical_parseval (f j))
  simpa only [coefficients,PiLp.norm_sq_eq_of_L2] using hh

def toCoefficientsLinear : Field→ₗ[ℂ]Coefficients where
  toFun f:=⟨coefficients f,by
    apply memℓp_gen
    simpa only [ENNReal.toReal_ofNat,Real.rpow_two] using (coefficients_hasSum f).summable⟩
  map_add' f g:=by
    ext n j
    change fourierIsometry (f j+g j) n=fourierIsometry (f j) n+fourierIsometry (g j) n
    rw [map_add]
    rfl
  map_smul' a f:=by
    ext n j
    change fourierIsometry (a • f j) n=a*fourierIsometry (f j) n
    rw [map_smul]
    rfl

theorem toCoefficients_norm (f : Field) : ‖toCoefficientsLinear f‖=‖f‖ := by
  have h1 := coefficients_hasSum f
  have h2 := hasSum_norm_square (toCoefficientsLinear f)
  have hs : ‖toCoefficientsLinear f‖^2=‖f‖^2 := h2.unique h1
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hs

def toCoefficientsIsometry : Field→ₗᵢ[ℂ]Coefficients where
  toLinearMap := toCoefficientsLinear
  norm_map' := toCoefficients_norm

theorem component_mem (v : Coefficients) (j : Fin 5) : Memℓp (fun n=>v n j) 2 := by
  apply memℓp_gen
  simp only [ENNReal.toReal_ofNat,Real.rpow_two]
  apply Summable.of_nonneg_of_le (fun n=>sq_nonneg _) _ (hasSum_norm_square v).summable
  intro n
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr (PiLp.norm_apply_le (v n) j)

def component (v : Coefficients) (j : Fin 5) : lp (fun _:Frequency=>ℂ) 2 :=
  ⟨fun n=>v n j,component_mem v j⟩

def fromCoefficients (v : Coefficients) : Field :=
  WithLp.toLp 2 (fun j=>fourierIsometry.symm (component v j))

theorem coefficients_surjective : Function.Surjective toCoefficientsIsometry := by
  intro v
  refine ⟨fromCoefficients v,?_⟩
  ext n j
  change fourierIsometry (fourierIsometry.symm (component v j)) n=v n j
  rw [fourierIsometry.apply_symm_apply]
  rfl

def vectorFourier : Field≃ₗᵢ[ℂ]Coefficients :=
  LinearIsometryEquiv.ofSurjective toCoefficientsIsometry coefficients_surjective

theorem vectorFourier_apply (f : Field) (n : Frequency) (j : Fin 5) :
    vectorFourier f n j=∫x,character (-n) x*f j x∂SpatialTorusNormalization.spatialHaar :=
  fourier_coefficient (f j) n

theorem full_vector_parseval (f : Field) :
    HasSum (fun n=>‖vectorFourier f n‖^2) (‖f‖^2) := coefficients_hasSum f

end
end Resonance.PhysicalVectorFourier
