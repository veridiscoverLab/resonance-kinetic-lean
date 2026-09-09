import Resonance.PhysicalVectorFourier
import Resonance.PhysicalFourierCharacters

/-! Finite coefficient vectors are precisely the original finite
trigonometric polynomials, as actual Haar-a.e. physical functions. -/
open MeasureTheory
open scoped ENNReal
namespace Resonance.PhysicalFourierPolynomials
noncomputable section
open PhysicalScalarFourier PhysicalVectorFourier SpatialTorusNormalization
open MatrixHilbertDictionary

def scalarSingle (n : Frequency) (a : ℂ) : PhysicalScalar :=
  fourierIsometry.symm (lp.single 2 n a)

theorem scalarSingle_basis (n : Frequency) (a : ℂ) :
    scalarSingle n a=toPhysical (a • UnitAddTorus.mFourierLp 2 n) := by
  apply fourierIsometry.injective
  rw [scalarSingle,fourierIsometry.apply_symm_apply]
  change lp.single 2 n a=UnitAddTorus.mFourierBasis.repr
    (toUnit (toPhysical (a • UnitAddTorus.mFourierLp 2 n)))
  rw [toUnit_toPhysical,map_smul,←UnitAddTorus.coe_mFourierBasis,
    HilbertBasis.repr_self]
  ext k
  by_cases hk:k=n <;> simp [lp.single_apply,hk]

theorem scalarSingle_ae (n : Frequency) (a : ℂ) :
    scalarSingle n a=ᵐ[spatialHaar] (fun x=>a*character n x) := by
  rw [scalarSingle_basis]
  have hp := Lp.coeFn_compMeasurePreserving (a • UnitAddTorus.mFourierLp 2 n) coordinates_preserving
  have hs := Lp.coeFn_smul a (UnitAddTorus.mFourierLp 2 n)
  have hb := UnitAddTorus.coeFn_mFourierLp 2 n
  have hsq := coordinates_preserving.quasiMeasurePreserving.ae hs
  have hbq := coordinates_preserving.quasiMeasurePreserving.ae hb
  filter_upwards [hp,hsq,hbq] with x hx hxs hxb
  change toPhysical (a • UnitAddTorus.mFourierLp 2 n) x=
    a*UnitAddTorus.mFourier n (coordinates x)
  change toPhysical (a • UnitAddTorus.mFourierLp 2 n) x=
    (a • UnitAddTorus.mFourierLp 2 n) (coordinates x) at hx
  rw [hx,hxs]
  change a*UnitAddTorus.mFourierLp 2 n (coordinates x)=_
  rw [hxb]

theorem inverse_component (v : Coefficients) (j : Fin 5) :
    fourierIsometry (vectorFourier.symm v j)=component v j := by
  apply Subtype.ext
  funext n
  have hh := congrArg (fun w:Coefficients=>w n j) (vectorFourier.apply_symm_apply v)
  exact hh

theorem vector_single_component (n : Frequency) (v : H) (j : Fin 5) :
    vectorFourier.symm (lp.single 2 n v) j=scalarSingle n (v j) := by
  apply fourierIsometry.injective
  rw [inverse_component,scalarSingle,fourierIsometry.apply_symm_apply]
  apply Subtype.ext
  funext k
  by_cases hk:k=n <;> simp [component,lp.single_apply,Pi.single_apply,hk]

theorem finite_polynomial_ae (S : Finset Frequency) (v : Frequency→H) (j : Fin 5) :
    (vectorFourier.symm (∑n∈S,lp.single 2 n (v n))) j=ᵐ[spatialHaar]
      (fun x=>∑n∈S,(v n j)*character n x) := by
  classical
  have he : (vectorFourier.symm (∑n∈S,lp.single 2 n (v n))) j=
      ∑n∈S,scalarSingle n (v n j) := by
    rw [map_sum]
    simp only [WithLp.ofLp_sum,Finset.sum_apply,vector_single_component]
  rw [he]
  clear he
  induction S using Finset.induction_on with
  | empty => simpa using (Lp.coeFn_zero ℂ 2 spatialHaar)
  | @insert n S hn ih =>
    simp only [Finset.sum_insert hn]
    filter_upwards [Lp.coeFn_add (scalarSingle n (v n j)) (∑k∈S,scalarSingle k (v k j)),
      scalarSingle_ae n (v n j),ih] with x hx h1 h2
    exact hx.trans (congrArg₂ (·+·) h1 h2)

end
end Resonance.PhysicalFourierPolynomials
