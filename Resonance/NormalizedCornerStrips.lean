import Resonance.RoleStripEvents

/-! A leg in a coordinate face opposite to the output lies in an
explicit far strip. The bound is for the original measurable event. -/
open Real Set MeasureTheory
open scoped ENNReal
namespace Resonance.NormalizedCornerStrips
noncomputable section
open ResonantMeasure CollisionFiber CollisionFrequency CubeAxisCoordinates CubeAxisScaling
open MarkedRelativeMass ActualStripEvents RoleStripEvents
set_option maxHeartbeats 1400000

def lowerFace (R ρ : ℝ) (l : Fin 4) (i : Fin 3) : Set FourMomenta :=
  {q | q l i∈Icc (-R) (-R+ρ)}

def fixedStrip (L : ℝ) (k : E) (l : Fin 4) (i : Fin 3) (a b : ℝ) : Set FourMomenta :=
  {q | ((q l-k) i)/L∈Icc a b}

theorem lowerFace_measurable (R ρ : ℝ) (l : Fin 4) (i : Fin 3) :
    MeasurableSet (lowerFace R ρ l i) := measurableSet_Icc.preimage (by fun_prop)

theorem lowerFace_eq_fixedStrip {L : ℝ} (hL : 0 < L) (d : Fin 3→ℝ)
    (t : ℝ) (l : Fin 4) (i : Fin 3) :
    lowerFace (L/2) (L*t) l i=
      fixedStrip L (L•normalizedOutput d) l i (-1+d i) (-1+d i+t) := by
  ext q
  change (-(L/2) ≤ q l i ∧ q l i ≤ -(L/2)+L*t) ↔
    (-1+d i ≤ (q l i-L*(1/2-d i))/L ∧
      (q l i-L*(1/2-d i))/L ≤ -1+d i+t)
  rw [le_div_iff₀ hL,div_le_iff₀ hL]
  constructor <;> rintro ⟨ha,hb⟩ <;> constructor <;> nlinarith

theorem fixedStrip_first_mass (R L : ℝ) (k : E) (i : Fin 3) (a b : ℝ) :
    fiberMeasure R k (fixedStrip L k 2 i a b)=fiberMeasure R k (axisStrip L i a b) := by
  apply measure_congr
  filter_upwards [fiber_support R k] with q hq
  apply propext
  change ((q 2-k) i)/L∈Icc a b ↔ ((q 2-q 0) i)/L∈Icc a b
  rw [hq.2]

theorem fixedStrip_second_mass (R L : ℝ) (k : E) (i : Fin 3) (a b : ℝ) :
    fiberMeasure R k (fixedStrip L k 3 i a b)=fiberMeasure R k (secondAxisStrip L i a b) := by
  apply measure_congr
  filter_upwards [fiber_support R k] with q hq
  apply propext
  change ((q 3-k) i)/L∈Icc a b ↔ ((q 3-q 0) i)/L∈Icc a b
  rw [hq.2]

theorem lowerFace_far {t di : ℝ} (ht : t ≤ (1:ℝ)/4096) (hdi : di ≤ t) :
    ∀s∈Icc ((-1+di)-t) ((-1+di+t)+t),(1:ℝ)/2 ≤ |s| := by
  intro s hs
  have hn := neg_le_abs s
  linarith [hs.2]

theorem original_opposite_lowerFace {L : ℝ} (hL : 0 < L) (i : Fin 3) {d : Fin 3→ℝ}
    {e t : ℝ} (he : 0 < e) (ht : 0 < t) (ht1 : t ≤ (1:ℝ)/4096) (het : e ≤ t)
    (hd0 : ∀j,0 ≤ d j) (hde : ∀j,d j ≤ e) (hmax : ∃j,d j=e) :
    fiberMeasure (L/2) (L•normalizedOutput d) (lowerFace (L/2) (L*t) 1 i) ≤
      ENNReal.ofReal ((152*relativeConstant)*t*geometricFrequency (L/2) (L•normalizedOutput d)) := by
  rw [lowerFace_eq_fixedStrip hL d t 1 i]
  have hm := original_opposite_strip_event hL i he (het.trans ht1) hd0 hde hmax
    (by norm_num : (0:ℝ) < 1/2) (by linarith : -1+d i ≤ -1+d i+t) ht
    (lowerFace_far ht1 ((hde i).trans het))
  apply hm.trans (ENNReal.ofReal_le_ofReal _)
  have hc : (4/(1/2:ℝ))*((-1+d i+t)-(-1+d i)+2*t+8*e/(1/2)) ≤ 152*t := by
    norm_num
    linarith
  have hr := mul_le_mul_of_nonneg_left hc relativeConstant_nonneg
  exact (mul_le_mul_of_nonneg_right hr (geometricFrequency_nonnegative _ _)).trans_eq (by ring)

theorem original_adjacent_lowerFace {L : ℝ} (hL : 0 < L) (i : Fin 3) {d : Fin 3→ℝ}
    {e t : ℝ} (he : 0 < e) (ht : 0 < t) (ht1 : t ≤ (1:ℝ)/4096) (het : e ≤ t)
    (hd0 : ∀j,0 ≤ d j) (hde : ∀j,d j ≤ e) (hmax : ∃j,d j=e)
    (l : Fin 4) (hl : l=2 ∨ l=3) :
    fiberMeasure (L/2) (L•normalizedOutput d) (lowerFace (L/2) (L*t) l i) ≤
      ENNReal.ofReal ((6*relativeConstant)*t*geometricFrequency (L/2) (L•normalizedOutput d)) := by
  have hk := (cube_smul_iff hL _).mpr (normalizedOutput_mem hd0
    (fun j => (hde j).trans (by linarith)))
  have hm := original_axis_strip_event hL i he (het.trans ht1) hd0 hde hmax
    (by norm_num : (0:ℝ) < 1/2) (by linarith : -1+d i ≤ -1+d i+t) ht
    (lowerFace_far ht1 ((hde i).trans het))
  have heq : relativeConstant*(((-1+d i+t)-(-1+d i)+2*t)/(1/2))=
      (6*relativeConstant)*t := by ring
  rw [heq] at hm
  rw [lowerFace_eq_fixedStrip hL d t l i]
  rcases hl with rfl|rfl
  · rw [fixedStrip_first_mass]
    exact hm
  · rw [fixedStrip_second_mass,second_axis_mass_eq (by positivity : 0 < L/2) _ hk]
    exact hm

end
end Resonance.NormalizedCornerStrips
