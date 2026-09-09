import Resonance.MarkedProductSymmetry

/-! A far sum strip and the same resonance product bound force one
coordinate into a slightly enlarged far strip. No root parametrization
or additional coarea theorem is needed. -/
open Real Set MeasureTheory
open scoped ENNReal
namespace Resonance.SumStripGeometry
noncomputable section
set_option maxHeartbeats 1000000

def farStrip (a b l δ : ℝ) : Set ℝ :=
  Icc (a-2*δ/l) (b+2*δ/l)∩{x | l/2≤|x|}

theorem farStrip_measurable (a b l δ : ℝ) : MeasurableSet (farStrip a b l δ) :=
  measurableSet_Icc.inter (measurableSet_le measurable_const (by fun_prop))

theorem product_controls_other {x y l δ : ℝ} (hl : 0<l)
    (hx : l/2≤|x|) (hp : |x*y|≤δ) : |y|≤2*δ/l := by
  rw [abs_mul] at hp
  apply (le_div_iff₀ hl).mpr
  nlinarith [abs_nonneg y]

theorem sum_strip_dichotomy {x y a b l δ : ℝ} (hl : 0<l)
    (hs : x+y∈Icc a b) (hfar : l≤|x+y|) (hp : |x*y|≤δ) :
    x∈farStrip a b l δ ∨ y∈farStrip a b l δ := by
  have hsum : l≤|x|+|y| := hfar.trans (abs_add_le x y)
  by_cases hx:l/2≤|x|
  · have hy := product_controls_other hl hx hp
    left
    refine ⟨⟨?_,?_⟩,hx⟩
    · linarith [hs.1,le_abs_self y]
    · linarith [hs.2,neg_le_abs y]
  · have hy : l/2≤|y| := by linarith
    have hx' := product_controls_other (x:=y) (y:=x) (δ:=δ) hl hy
      (by simpa only [mul_comm y x] using hp)
    right
    refine ⟨⟨?_,?_⟩,hy⟩
    · linarith [hs.1,le_abs_self x]
    · linarith [hs.2,neg_le_abs x]

theorem farStrip_inverse_bound (a b δ : ℝ) {l : ℝ} (hl : 0<l) :
    ∀x∈farStrip a b l δ,|x⁻¹|≤2/l := by
  intro x hx
  rw [abs_inv]
  have h := one_div_le_one_div_of_le (by linarith : 0<l/2) hx.2
  convert h using 1 <;> field_simp

theorem farStrip_volume_bound (a b l δ : ℝ) :
    (volume:Measure ℝ) (farStrip a b l δ)≤ENNReal.ofReal (b-a+4*δ/l) := by
  have h := measure_mono (μ:=(volume:Measure ℝ))
    (show farStrip a b l δ⊆Icc (a-2*δ/l) (b+2*δ/l) from fun _ hx=>hx.1)
  rw [Real.volume_Icc] at h
  convert h using 1
  congr 1
  ring

theorem marked_sum_strip_envelope {a b l δ : ℝ} (hl : 0<l)
    (hfar : ∀s∈Icc a b,l≤|s|) {w : ℝ×ℝ→ℝ≥0∞} (hb : ∀p,w p≤1)
    (hs : ∀p,p.1+p.2∉Icc a b→w p=0) (p : ℝ×ℝ) :
    MarkedProductSymmetry.productCut δ w p≤
      (farStrip a b l δ).indicator (fun _=>1) p.1+
      (farStrip a b l δ).indicator (fun _=>1) p.2 := by
  classical
  by_cases ht:|p.1*p.2|≤δ
  · rw [MarkedProductSymmetry.productCut,indicator_of_mem
      (show p∈{p:ℝ×ℝ | |p.1*p.2|≤δ} from ht)]
    by_cases hp:p.1+p.2∈Icc a b
    · rcases sum_strip_dichotomy hl hp (hfar _ hp) ht with h1|h2
      · rw [indicator_of_mem h1]
        exact (hb p).trans (le_add_right le_rfl)
      · rw [indicator_of_mem h2]
        exact (hb p).trans (le_add_left le_rfl)
    · rw [hs p hp]
      exact zero_le _
  · rw [MarkedProductSymmetry.productCut,indicator_of_notMem
      (show p∉{p:ℝ×ℝ | |p.1*p.2|≤δ} from ht)]
    exact zero_le _

end
end Resonance.SumStripGeometry
