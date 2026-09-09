import Resonance.CornerConvolutionBounds

/-! Exact six-sign decomposition of the original three-axis zero density.
All transformations are on the same nonnegative integral. -/
open Real Set MeasureTheory
open scoped ENNReal Topology
namespace Resonance.CornerConvolutionSigns
noncomputable section
set_option maxHeartbeats 800000
open Resonance.CornerConvolution Resonance.CornerConvolutionBounds
open Resonance.AxisProductDensity Resonance.TriangleProductDensity
open Resonance.CornerProductDensity

def negativeLift (d t:ℝ) : ℝ≥0∞ := negativeDensity d (-t)
def tripleZero (a b c:ℝ→ℝ≥0∞) : ℝ≥0∞ :=
  ∫⁻s:ℝ,∫⁻t:ℝ,a s*b t*c (-s-t)

theorem negativeLift_measurable (d:ℝ) : Measurable (negativeLift d) :=
  (negativeDensity_measurable d).comp measurable_neg

theorem positiveDensity_zero {d t:ℝ} (ht:t≤0) : positiveDensity d t=0 := by
  simp [positiveDensity,triangleDensity,not_lt.mpr ht]
theorem negativeDensity_zero {d t:ℝ} (ht:t≤0) : negativeDensity d t=0 := by
  simp [negativeDensity,rectangleDensity,not_lt.mpr ht]
theorem axisDensity_split (d t:ℝ) :
    axisDensity d t=positiveDensity d t+negativeLift d t := rfl

theorem lintegral_positive_support (f:ℝ→ℝ≥0∞) (hf:∀x,x≤0→f x=0) :
    (∫⁻x:ℝ,f x)=∫⁻x in Ioi (0:ℝ),f x := by
  rw [←lintegral_indicator measurableSet_Ioi]
  apply lintegral_congr
  intro x
  by_cases hx:0<x
  · simp [hx]
  · simp [hx,hf x (le_of_not_gt hx)]

theorem tripleZero_swap_first (a b c:ℝ→ℝ≥0∞)
    (ha:Measurable a) (hb:Measurable b) (hc:Measurable c) :
    tripleZero a b c=tripleZero b a c := by
  unfold tripleZero
  rw [lintegral_lintegral_swap (by fun_prop)]
  apply lintegral_congr
  intro s
  apply lintegral_congr
  intro t
  rw [show -t-s=-s-t by ring]
  ring

theorem tripleZero_swap_last (a b c:ℝ→ℝ≥0∞) :
    tripleZero a b c=tripleZero a c b := by
  unfold tripleZero
  apply lintegral_congr
  intro s
  have he := lintegral_sub_left_eq_self (μ:=(volume:Measure ℝ))
    (fun t:ℝ=>a s*b t*c (-s-t)) (-s)
  have hcancel (t:ℝ) : -s-(-s-t)=t := by ring
  rw [←he]
  apply lintegral_congr
  intro t
  rw [hcancel]
  ring

theorem tripleZero_add_first (a a' b c:ℝ→ℝ≥0∞)
    (ha:Measurable a) (hb:Measurable b) (hc:Measurable c) :
    tripleZero (a+a') b c=tripleZero a b c+tripleZero a' b c := by
  unfold tripleZero
  simp only [Pi.add_apply,add_mul]
  have hm (s:ℝ) : Measurable (fun t:ℝ=>a s*b t*c (-s-t)) := by fun_prop
  simp_rw [lintegral_add_left (hm _)]
  exact lintegral_add_left (show Measurable (fun s:ℝ=>∫⁻t:ℝ,a s*b t*c (-s-t)) from
    (show Measurable (fun p:ℝ×ℝ=>a p.1*b p.2*c (-p.1-p.2)) by fun_prop).lintegral_prod_right') _

theorem tripleZero_add_last (a b c c':ℝ→ℝ≥0∞)
    (ha:Measurable a) (hb:Measurable b) (hc:Measurable c) :
    tripleZero a b (c+c')=tripleZero a b c+tripleZero a b c' := by
  unfold tripleZero
  simp only [Pi.add_apply,mul_add]
  have hm (s:ℝ) : Measurable (fun t:ℝ=>a s*b t*c (-s-t)) := by fun_prop
  simp_rw [lintegral_add_left (hm _)]
  exact lintegral_add_left (show Measurable (fun s:ℝ=>∫⁻t:ℝ,a s*b t*c (-s-t)) from
    (show Measurable (fun p:ℝ×ℝ=>a p.1*b p.2*c (-p.1-p.2)) by fun_prop).lintegral_prod_right') _

theorem tripleZero_add_middle (a b b' c:ℝ→ℝ≥0∞)
    (ha:Measurable a) (hb:Measurable b) (hc:Measurable c) :
    tripleZero a (b+b') c=tripleZero a b c+tripleZero a b' c := by
  rw [tripleZero_swap_last, tripleZero_add_last a c b b' ha hc hb,
    tripleZero_swap_last a c b,tripleZero_swap_last a c b']

theorem tripleZero_all_positive (di dl dj:ℝ) :
    tripleZero (positiveDensity di) (positiveDensity dl) (positiveDensity dj)=0 := by
  unfold tripleZero
  have hp (s t:ℝ) : positiveDensity di s*positiveDensity dl t*positiveDensity dj (-s-t)=0 := by
    by_cases hs:0<s
    · by_cases ht:0<t
      · rw [positiveDensity_zero (by linarith:-s-t≤0)]; simp
      · rw [positiveDensity_zero (le_of_not_gt ht)]; simp
    · rw [positiveDensity_zero (le_of_not_gt hs)]; simp
  simp_rw [hp]
  simp

theorem tripleZero_all_negative (di dl dj:ℝ) :
    tripleZero (negativeLift di) (negativeLift dl) (negativeLift dj)=0 := by
  unfold tripleZero negativeLift
  have hp (s t:ℝ) : negativeDensity di (-s)*negativeDensity dl (-t)*
      negativeDensity dj (-(-s-t))=0 := by
    by_cases hs:0< -s
    · by_cases ht:0< -t
      · rw [negativeDensity_zero (by linarith:-(-s-t)≤0)]; simp
      · rw [negativeDensity_zero (le_of_not_gt ht)]; simp
    · rw [negativeDensity_zero (le_of_not_gt hs)]; simp
  simp_rw [hp]
  simp

theorem tripleZero_one_negative (dj di dl:ℝ) :
    tripleZero (negativeLift dj) (positiveDensity di) (positiveDensity dl)=
      oneNegative dj di dl := by
  unfold tripleZero negativeLift
  rw [←lintegral_neg_eq_self (fun s:ℝ=>∫⁻t:ℝ,
    negativeDensity dj (-s)*positiveDensity di t*positiveDensity dl (-s-t))]
  simp only [neg_neg]
  have ht (s:ℝ) : (∫⁻t:ℝ,negativeDensity dj s*positiveDensity di t*positiveDensity dl (s-t))=
      negativeDensity dj s*positiveConvolution di dl s := by
    unfold positiveConvolution
    rw [←lintegral_const_mul (μ:=(volume:Measure ℝ).restrict (Ioo 0 s))
      (negativeDensity dj s)
      (show Measurable (fun t=>positiveDensity di t*positiveDensity dl (s-t)) from
        (positiveDensity_measurable di).mul
          ((positiveDensity_measurable dl).comp (measurable_const.sub measurable_id)))]
    rw [←lintegral_indicator (show MeasurableSet (Ioo (0:ℝ) s) from measurableSet_Ioo)]
    apply lintegral_congr
    intro t
    by_cases h:0<t ∧ t<s
    · simp [h,mul_assoc]
    · have hz : positiveDensity di t*positiveDensity dl (s-t)=0 := by
        by_cases h0:0<t
        · have h1 : s-t≤0 := by rcases not_and.mp h h0 with hh; linarith
          rw [positiveDensity_zero h1]; simp
        · rw [positiveDensity_zero (le_of_not_gt h0)]; simp
      simp only [indicator_apply,mem_Ioo,if_neg h]
      rw [mul_assoc,hz,mul_zero]
  simp_rw [ht]
  exact lintegral_positive_support _ (fun s hs=>by rw [negativeDensity_zero hs,zero_mul])

theorem tripleZero_two_negative (di dl dj:ℝ) :
    tripleZero (negativeLift di) (negativeLift dl) (positiveDensity dj)=
      twoNegative di dl dj := by
  unfold tripleZero negativeLift
  rw [←lintegral_neg_eq_self (fun s:ℝ=>∫⁻t:ℝ,
    negativeDensity di (-s)*negativeDensity dl (-t)*positiveDensity dj (-s-t))]
  simp only [neg_neg]
  have ht (s:ℝ) : (∫⁻t:ℝ,negativeDensity di s*negativeDensity dl (-t)*positiveDensity dj (s-t))=
      negativeDensity di s*(∫⁻t in Ioi (0:ℝ),negativeDensity dl t*positiveDensity dj (s+t)) := by
    rw [←lintegral_neg_eq_self (fun t:ℝ=>negativeDensity di s*
      negativeDensity dl (-t)*positiveDensity dj (s-t))]
    simp only [neg_neg,sub_neg_eq_add]
    have hm : Measurable (fun t:ℝ=>negativeDensity dl t*positiveDensity dj (s+t)) :=
      (negativeDensity_measurable dl).mul
        ((positiveDensity_measurable dj).comp (measurable_const.add measurable_id))
    simp_rw [mul_assoc]
    rw [lintegral_const_mul _ hm]
    congr 1
    exact lintegral_positive_support _ (fun t ht=>by rw [negativeDensity_zero ht,zero_mul])
  simp_rw [ht]
  exact lintegral_positive_support _ (fun s hs=>by rw [negativeDensity_zero hs,zero_mul])

theorem tripleZero_rotate (a b c:ℝ→ℝ≥0∞)
    (ha:Measurable a) (hb:Measurable b) (hc:Measurable c) :
    tripleZero a b c=tripleZero c a b := by
  rw [tripleZero_swap_last a b c,tripleZero_swap_first a c b ha hc hb]

/-- Exactly the six nonzero sign patterns of the original zero-energy
integral; the all-positive and all-negative patterns vanish identically. -/
theorem sumDensity_six_signs (d:Fin 3→ℝ) :
    sumDensity d 0=
      oneNegative (d 0) (d 1) (d 2)+
      oneNegative (d 1) (d 0) (d 2)+
      oneNegative (d 2) (d 0) (d 1)+
      twoNegative (d 0) (d 1) (d 2)+
      twoNegative (d 0) (d 2) (d 1)+
      twoNegative (d 1) (d 2) (d 0) := by
  let P := fun i:Fin 3=>positiveDensity (d i)
  let N := fun i:Fin 3=>negativeLift (d i)
  have hP (i:Fin 3) : Measurable (P i) := positiveDensity_measurable _
  have hN (i:Fin 3) : Measurable (N i) := negativeLift_measurable _
  have he : sumDensity d 0=tripleZero (P 0+N 0) (P 1+N 1) (P 2+N 2) := by
    simp only [sumDensity,tripleZero,zero_sub,axisDensity_split,Pi.add_apply,P,N]
  rw [he,tripleZero_add_first (P 0) (N 0) (P 1+N 1) (P 2+N 2)
      (hP 0) ((hP 1).add (hN 1)) ((hP 2).add (hN 2)),
    tripleZero_add_middle (P 0) (P 1) (N 1) (P 2+N 2) (hP 0) (hP 1) ((hP 2).add (hN 2)),
    tripleZero_add_middle (N 0) (P 1) (N 1) (P 2+N 2) (hN 0) (hP 1) ((hP 2).add (hN 2)),
    tripleZero_add_last (P 0) (P 1) (P 2) (N 2) (hP 0) (hP 1) (hP 2),
    tripleZero_add_last (P 0) (N 1) (P 2) (N 2) (hP 0) (hN 1) (hP 2),
    tripleZero_add_last (N 0) (P 1) (P 2) (N 2) (hN 0) (hP 1) (hP 2),
    tripleZero_add_last (N 0) (N 1) (P 2) (N 2) (hN 0) (hN 1) (hP 2)]
  rw [tripleZero_rotate (P 0) (P 1) (N 2) (hP 0) (hP 1) (hN 2),
    tripleZero_swap_first (P 0) (N 1) (P 2) (hP 0) (hN 1) (hP 2),
    tripleZero_swap_first (P 0) (N 1) (N 2) (hP 0) (hN 1) (hN 2),
    tripleZero_swap_last (N 1) (P 0) (N 2),
    tripleZero_swap_last (N 0) (P 1) (N 2)]
  dsimp [P,N]
  rw [tripleZero_all_positive,tripleZero_all_negative]
  simp only [tripleZero_one_negative,tripleZero_two_negative]
  ring

theorem sumDensity_rotate (d:Fin 3→ℝ) :
    sumDensity d 0=sumDensity ![d 2,d 0,d 1] 0 := by
  have h := tripleZero_rotate (axisDensity (d 0)) (axisDensity (d 1)) (axisDensity (d 2))
    (axisDensity_measurable _) (axisDensity_measurable _) (axisDensity_measurable _)
  simpa only [sumDensity,tripleZero,zero_sub,Matrix.cons_val_zero,Matrix.cons_val_one,
    Matrix.cons_val_two] using h

end
end Resonance.CornerConvolutionSigns
