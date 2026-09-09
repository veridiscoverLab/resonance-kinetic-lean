import Resonance.LocalMarkedConvolution
import Resonance.SumStripDensity

/-! Original fixed-output mass of a far opposite-leg sum strip, paid
by the full resonance product range and the original frequency. -/
open Real Set MeasureTheory
open scoped ENNReal
namespace Resonance.SumStripMass
noncomputable section
open PlaneCoarea CubeAxisCoordinates MarkedProductDensity MarkedProductBounds
open MarkedDensityContinuity MarkedRelativeMass MarkedPhysicalScaling LocalMarkedConvolution
open SumStripDensity
set_option maxHeartbeats 1000000

theorem original_local_marked_mass {L : ℝ} (hL : 0<L) {d : Fin 3→ℝ} {e B : ℝ}
    (he : 0<e) (he1 : e≤(1:ℝ)/4096) (hd0 : ∀i,0≤d i) (hde : ∀i,d i≤e)
    (hmax : ∃i,d i=e) (hB : 0≤B) {w : ℝ×ℝ→ℝ}
    (hw : Continuous w) (hp : ∀p,0≤w p) (hb : ∀p,w p≤1)
    (hbound : ∀ᵐ t ∂(volume:Measure ℝ),|t|≤2*e→
      productDensity (markedWeight (d 0) (fun p=>ENNReal.ofReal (w p))) t≤ENNReal.ofReal B) :
    FiberContinuity.fiberReadout (L/2) (scaledMark L w) (L•normalizedOutput d)≤
      relativeConstant*B*CollisionFrequency.geometricFrequency (L/2) (L•normalizedOutput d) := by
  have hd1 : ∀i,d i<1 := fun i=>lt_of_le_of_lt (hde i) (by linarith)
  have hm := congrArg ENNReal.toReal (original_scaled_marked_frequency hL hd0 hd1 hw hp hb)
  have hn := congrArg ENNReal.toReal
    (CollisionFrequencyConvolution.original_frequency_eq_convolution hL hd0 hd1)
  have hp0 : 0≤FiberContinuity.fiberReadout (L/2) (scaledMark L w) (L•normalizedOutput d) :=
    integral_nonneg (fun q=>hp _)
  simp only [ENNReal.toReal_ofReal hp0,ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (by positivity : 0≤L^4/2)] at hm
  simp only [ENNReal.toReal_ofReal (CollisionFrequency.geometricFrequency_nonnegative _ _),
    ENNReal.toReal_mul,ENNReal.toReal_ofReal (by positivity : 0≤L^4/2)] at hn
  rw [hm,hn]
  have h := original_local_relative_bound he he1 hd0 hde hmax hB _ hbound
    (marked_density_le_original (hd0 0) (hd1 0) _ (fun p=>ENNReal.ofReal_le_one.mpr (hb p)))
  exact (mul_le_mul_of_nonneg_left h (by positivity : 0≤L^4/2)).trans_eq (by ring)

theorem original_far_sum_strip_mass {L : ℝ} (hL : 0<L) {d : Fin 3→ℝ} {e l a b : ℝ}
    (he : 0<e) (he1 : e≤(1:ℝ)/4096) (hd0 : ∀i,0≤d i) (hde : ∀i,d i≤e)
    (hmax : ∃i,d i=e) (hl : 0<l) (hab : a≤b) (hfar : ∀s∈Icc a b,l≤|s|)
    {w : ℝ×ℝ→ℝ} (hw : Continuous w) (hp : ∀p,0≤w p) (hb : ∀p,w p≤1)
    (hs : ∀p,p.1+p.2∉Icc a b→w p=0) :
    FiberContinuity.fiberReadout (L/2) (scaledMark L w) (L•normalizedOutput d)≤
      relativeConstant*((4/l)*(b-a+8*e/l))*
        CollisionFrequency.geometricFrequency (L/2) (L•normalizedOutput d) := by
  apply original_local_marked_mass hL he he1 hd0 hde hmax
    (mul_nonneg (by positivity) (add_nonneg (sub_nonneg.mpr hab) (by positivity))) hw hp hb
  have h := original_local_sum_strip_bound (δ:=2*e) (d 0) hl hfar hb hs
  have heq : 4*(2*e)/l=8*e/l := by ring
  simpa only [heq] using h

theorem original_far_sum_strip_width {L : ℝ} (hL : 0<L) {d : Fin 3→ℝ} {e η l a b : ℝ}
    (he : 0<e) (he1 : e≤(1:ℝ)/4096) (hd0 : ∀i,0≤d i) (hde : ∀i,d i≤e)
    (hmax : ∃i,d i=e) (hl : 0<l) (hab : a≤b) (hwidth : b-a≤η) (heη : e≤η)
    (hfar : ∀s∈Icc a b,l≤|s|) {w : ℝ×ℝ→ℝ}
    (hw : Continuous w) (hp : ∀p,0≤w p) (hb : ∀p,w p≤1)
    (hs : ∀p,p.1+p.2∉Icc a b→w p=0) :
    FiberContinuity.fiberReadout (L/2) (scaledMark L w) (L•normalizedOutput d)≤
      (relativeConstant*(4/l)*(1+8/l))*η*
        CollisionFrequency.geometricFrequency (L/2) (L•normalizedOutput d) := by
  have hcoeff : b-a+8*e/l≤(1+8/l)*η := by
    have h := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left heη (by norm_num : (0:ℝ)≤8)) hl.le
    exact (add_le_add hwidth h).trans_eq (by ring)
  calc
    _ ≤ relativeConstant*((4/l)*(b-a+8*e/l))*
        CollisionFrequency.geometricFrequency (L/2) (L•normalizedOutput d) :=
      original_far_sum_strip_mass hL he he1 hd0 hde hmax hl hab hfar hw hp hb hs
    _ ≤ relativeConstant*((4/l)*((1+8/l)*η))*
        CollisionFrequency.geometricFrequency (L/2) (L•normalizedOutput d) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hcoeff (by positivity)) relativeConstant_nonneg)
        (CollisionFrequency.geometricFrequency_nonnegative _ _)
    _ = _ := by ring

end
end Resonance.SumStripMass
