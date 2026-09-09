import Resonance.PlaneCoarea
import Mathlib.Analysis.InnerProductSpace.GramMatrix
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-! Exact normalized Hausdorff area of actual two-dimensional linear images.
The density is the square root of the Gram determinant, derived from a genuine
orthonormal frame and the Lebesgue determinant theorem. -/
open Real Set MeasureTheory
open scoped ENNReal InnerProductSpace EuclideanGeometry
namespace Resonance.LinearSurfaceArea
noncomputable section
abbrev P := EuclideanSpace ℝ (Fin 2)
abbrev A := EuclideanSpace ℝ (Fin 3)
def e (i:Fin 2) : P := EuclideanSpace.single i 1

def gramJacobian (L:P→L[ℝ]A) : ℝ := Real.sqrt
  (inner ℝ (L (e 0)) (L (e 0))*inner ℝ (L (e 1)) (L (e 1))
    -(inner ℝ (L (e 0)) (L (e 1)))^2)

theorem gramJacobian_nonneg (L:P→L[ℝ]A) : 0≤gramJacobian L := Real.sqrt_nonneg _

theorem exists_isometric_factor {L:P→L[ℝ]A} (hL:Function.Injective L) :
    ∃(i:P→ₗᵢ[ℝ]A)(S:P→L[ℝ]P),Function.Injective S ∧ ∀x,i (S x)=L x := by
  let V := LinearMap.range L.toLinearMap
  have hd : Module.finrank ℝ V=2 := by
    rw [LinearMap.finrank_range_of_inj hL]
    simp [P]
  let b : OrthonormalBasis (Fin 2) ℝ V := (stdOrthonormalBasis ℝ V).reindex (finCongr hd)
  let i:P→ₗᵢ[ℝ]A := V.subtypeₗᵢ.comp b.repr.symm.toLinearIsometry
  let S:P→L[ℝ]P := b.repr.toContinuousLinearEquiv.toContinuousLinearMap.comp
    (L.codRestrict V (fun x=>⟨x,rfl⟩))
  have hi:∀x,i (S x)=L x := by
    intro x
    change ((b.repr.symm (b.repr ⟨L x,⟨x,rfl⟩⟩)):A)=L x
    simp
  refine ⟨i,S,?_,hi⟩
  intro x y hxy
  apply hL
  rw [←hi x,←hi y,hxy]

theorem determinant_sq_gram (S:P→L[ℝ]P) :
    (LinearMap.det S.toLinearMap)^2=
      inner ℝ (S (e 0)) (S (e 0))*inner ℝ (S (e 1)) (S (e 1))
        -(inner ℝ (S (e 0)) (S (e 1)))^2 := by
  rw [←LinearMap.det_toMatrix (PiLp.basisFun 2 ℝ (Fin 2))]
  simp only [Matrix.det_fin_two,LinearMap.toMatrix_apply,PiLp.basisFun_repr,PiLp.basisFun_apply,
    PiLp.inner_apply,Fin.sum_univ_two]
  simp only [e,EuclideanSpace.single,Resonance.PlaneCoarea.real_inner_apply]
  change (S (e 0) 0*S (e 1) 1-S (e 1) 0*S (e 0) 1)^2=
    (S (e 0) 0*S (e 0) 0+S (e 0) 1*S (e 0) 1)*
      (S (e 1) 0*S (e 1) 0+S (e 1) 1*S (e 1) 1)
      -(S (e 1) 0*S (e 0) 0+S (e 1) 1*S (e 0) 1)^2
  ring

theorem gramJacobian_isometric_factor (L:P→L[ℝ]A) (i:P→ₗᵢ[ℝ]A) (S:P→L[ℝ]P)
    (hf:∀x,i (S x)=L x) : gramJacobian L=|LinearMap.det S.toLinearMap| := by
  unfold gramJacobian
  simp_rw [←hf,i.inner_map_map]
  rw [←determinant_sq_gram,Real.sqrt_sq_eq_abs]

theorem linear_image_area {L:P→L[ℝ]A} (hL:Function.Injective L) (s:Set P) :
    (μHE[2]:Measure A) (L '' s)=ENNReal.ofReal (gramJacobian L)*(volume:Measure P) s := by
  obtain ⟨i,S,_hS,hf⟩ := exists_isometric_factor hL
  have himage : L '' s=i '' (S '' s) := by
    rw [←image_comp]
    congr 1
    funext x
    exact (hf x).symm
  rw [himage,i.isometry.euclideanHausdorffMeasure_image,
    EuclideanSpace.euclideanHausdorffMeasure_eq_volume,
    Measure.addHaar_image_continuousLinearMap,gramJacobian_isometric_factor L i S hf]

def graphLinear (l:P→L[ℝ]ℝ) : P→L[ℝ]A :=
  ({toFun:=fun x=>WithLp.toLp 2 ![x 0,l x,x 1]
    map_add':=by intros; ext j; fin_cases j <;> simp
    map_smul':=by intros; ext j; fin_cases j <;> simp}:P→ₗ[ℝ]A).toContinuousLinearMap

theorem graphLinear_injective (l:P→L[ℝ]ℝ) : Function.Injective (graphLinear l) := by
  intro x y h
  ext i
  fin_cases i
  · exact congrArg (fun z:A=>z 0) h
  · exact congrArg (fun z:A=>z 2) h

theorem graphLinear_gram (l:P→L[ℝ]ℝ) :
    gramJacobian (graphLinear l)=Real.sqrt (1+(l (e 0))^2+(l (e 1))^2) := by
  unfold gramJacobian
  congr 1
  simp [graphLinear,e,PiLp.inner_apply,Fin.sum_univ_three,
    Resonance.PlaneCoarea.real_inner_apply]
  simp only [EuclideanSpace.real_norm_sq_eq,Fin.sum_univ_three]
  dsimp
  ring

end
end Resonance.LinearSurfaceArea
