import Resonance.PinnedOperator
import Resonance.ComplexBoundedMultiplier

/-! Actual physical relative variables on the pinned momentum circle.
The same positive profile determines its quartet weight and multiplication
map; its latter action is bounded and invertible, without being unitary. -/
open MeasureTheory Set
open scoped ENNReal
namespace Resonance.PinnedPhysicalMultiplier
noncomputable section
open PinnedPeriodicity PinnedEndToEnd PinnedMaximalDifference PinnedClassificationFinal
local notation "Circle" => PinnedPeriodicity.Circle
local instance periodPositive : Fact (0 < period) := ⟨period_pos⟩

theorem dispersion_positive {d : ℝ} (hd0 : 0 < d) (hdU : d < 1/2) (x : Circle) :
    0 < circleDispersion d x := by
  induction x using Quotient.inductionOn with
  | h x => exact PinnedGeometry.signed_omega_pos (by linarith) hdU x

def physicalWeight (d : ℝ) (N : C(Circle,ℝ)) (k : FourCircle) : ℝ :=
  ∏i,N (k i)/circleDispersion d (k i)

theorem physicalWeight_formula (d : ℝ) (N : C(Circle,ℝ)) (k : FourCircle) :
    physicalWeight d N k=(∏i,N (k i))/(∏i,circleDispersion d (k i)) := by
  simp only [physicalWeight, Finset.prod_div_distrib]

theorem physicalWeight_continuous {d : ℝ} (hd0 : 0 < d) (hdU : d < 1/2)
    (N : C(Circle,ℝ)) : Continuous (physicalWeight d N) := by
  apply continuous_finset_prod
  intro i _
  exact (N.continuous.comp (continuous_apply i)).div
    ((circleDispersion_continuous hd0 hdU).comp (continuous_apply i))
    (fun k=>(dispersion_positive hd0 hdU (k i)).ne')

theorem physicalWeight_positive {d : ℝ} (hd0 : 0 < d) (hdU : d < 1/2)
    (N : C(Circle,ℝ)) (hN : ∀x,0 < N x) (k : FourCircle) :
    0 < physicalWeight d N k :=
  Finset.prod_pos (fun i _=>div_pos (hN (k i)) (dispersion_positive hd0 hdU (k i)))

def divideWeight (N : C(Circle,ℝ)) (x : Circle) : ℂ := ((N x)⁻¹ : ℝ)
def multiplyWeight (N : C(Circle,ℝ)) (x : Circle) : ℂ := N x

theorem divideWeight_continuous (N : C(Circle,ℝ)) (hN : ∀x,0 < N x) :
    Continuous (divideWeight N) :=
  Complex.continuous_ofReal.comp (N.continuous.inv₀ (fun x=>(hN x).ne'))

theorem divideWeight_memLp (N : C(Circle,ℝ)) (hN : ∀x,0 < N x) :
    MemLp (divideWeight N) ∞ circleHaar :=
  (divideWeight_continuous N hN).memLp_top_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _) circleHaar

theorem multiplyWeight_memLp (N : C(Circle,ℝ)) :
    MemLp (multiplyWeight N) ∞ circleHaar :=
  (Complex.continuous_ofReal.comp N.continuous).memLp_top_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _) circleHaar

theorem weight_inverse (N : C(Circle,ℝ)) (hN : ∀x,0 < N x) :
    ∀ᵐx∂circleHaar,divideWeight N x*multiplyWeight N x=1 := by
  filter_upwards [] with x
  simp [divideWeight,multiplyWeight,(hN x).ne']

def physicalEquivalence (N : C(Circle,ℝ)) (hN : ∀x,0 < N x) : Source≃L[ℂ]Source :=
  ComplexBoundedMultiplier.equivalence (divideWeight_memLp N hN)
    (multiplyWeight_memLp N) (weight_inverse N hN)

theorem physicalEquivalence_ae (N : C(Circle,ℝ)) (hN : ∀x,0 < N x) (f : Source) :
    physicalEquivalence N hN f=ᵐ[circleHaar] (fun x=>f x/(N x : ℂ)) := by
  have hh := ComplexBoundedMultiplier.equivalence_ae (divideWeight_memLp N hN)
    (multiplyWeight_memLp N) (weight_inverse N hN) f
  simpa only [physicalEquivalence,divideWeight,Complex.ofReal_inv,div_eq_mul_inv] using hh

theorem physicalEquivalence_inverse_ae (N : C(Circle,ℝ)) (hN : ∀x,0 < N x) (f : Source) :
    (physicalEquivalence N hN).symm f=ᵐ[circleHaar] (fun x=>f x*(N x : ℂ)) :=
  ComplexBoundedMultiplier.inverse_equivalence_ae (divideWeight_memLp N hN)
    (multiplyWeight_memLp N) (weight_inverse N hN) f

theorem physical_inverse_bound (N : C(Circle,ℝ)) (hN : ∀x,0 < N x) (f : Source) :
    ‖(physicalEquivalence N hN).symm f‖ ≤ ‖N‖*‖f‖ := by
  apply ComplexBoundedMultiplier.vector_bound (multiplyWeight_memLp N)
  filter_upwards [] with x
  simpa only [multiplyWeight,Complex.norm_real] using N.norm_coe_le_norm x

end
end Resonance.PinnedPhysicalMultiplier
