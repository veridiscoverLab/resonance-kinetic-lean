import Resonance.PhysicalNonlinear

/-! Quantitative L² continuity of the original full cubic collision output
on sets with a common physical amplitude bound. The bound does not assert
that any nonlinear evolution remains in such a set. -/
open MeasureTheory
open scoped ENNReal

namespace Resonance.NonlinearContinuity
noncomputable section
open Collision ResonantMeasure PhysicalMarginal PhysicalCollisionForm PhysicalNonlinear

theorem triple_difference_bound {B a b c A D C : ℝ} (hB : 0 ≤ B)
    (_ha : |a| ≤ B) (hb : |b| ≤ B) (hc : |c| ≤ B)
    (hA : |A| ≤ B) (hD : |D| ≤ B) (_hC : |C| ≤ B) :
    |a * b * c - A * D * C| ≤ B ^ 2 * (|a-A| + |b-D| + |c-C|) := by
  have hbc : |b| * |c| ≤ B ^ 2 := by nlinarith [mul_le_mul hb hc (abs_nonneg c) hB]
  have hAc : |A| * |c| ≤ B ^ 2 := by nlinarith [mul_le_mul hA hc (abs_nonneg c) hB]
  have hAD : |A| * |D| ≤ B ^ 2 := by nlinarith [mul_le_mul hA hD (abs_nonneg D) hB]
  have h1 := mul_le_mul_of_nonneg_left hbc (abs_nonneg (a-A))
  have h2 := mul_le_mul_of_nonneg_left hAc (abs_nonneg (b-D))
  have h3 := mul_le_mul_of_nonneg_left hAD (abs_nonneg (c-C))
  calc
    |a*b*c-A*D*C| = |(a-A)*b*c + A*(b-D)*c + A*D*(c-C)| := congrArg abs (by ring)
    _ ≤ |(a-A)*b*c + A*(b-D)*c| + |A*D*(c-C)| := abs_add_le _ _
    _ ≤ (|(a-A)*b*c| + |A*(b-D)*c|) + |A*D*(c-C)| := by gcongr; exact abs_add_le _ _
    _ ≤ _ := by simp only [abs_mul]; nlinarith

theorem cubic_difference_bound {B : ℝ} (hB : 0 ≤ B) (f g : Quartet)
    (hf : ∀ i, |f i| ≤ B) (hg : ∀ i, |g i| ≤ B) :
    |collisionPolynomial f - collisionPolynomial g| ≤
      3 * B ^ 2 * (|f 0-g 0| + |f 1-g 1| + |f 2-g 2| + |f 3-g 3|) := by
  have h123 := triple_difference_bound hB (hf 1) (hf 2) (hf 3) (hg 1) (hg 2) (hg 3)
  have h023 := triple_difference_bound hB (hf 0) (hf 2) (hf 3) (hg 0) (hg 2) (hg 3)
  have h013 := triple_difference_bound hB (hf 0) (hf 1) (hf 3) (hg 0) (hg 1) (hg 3)
  have h012 := triple_difference_bound hB (hf 0) (hf 1) (hf 2) (hg 0) (hg 1) (hg 2)
  let a := f 1*f 2*f 3-g 1*g 2*g 3
  let b := f 0*f 2*f 3-g 0*g 2*g 3
  let c := f 0*f 1*f 3-g 0*g 1*g 3
  let d := f 0*f 1*f 2-g 0*g 1*g 2
  have he : collisionPolynomial f - collisionPolynomial g = a+b-c-d := by
    dsimp [collisionPolynomial, a, b, c, d]
    ring
  rw [he]
  calc
    |a+b-c-d| ≤ |a+b-c| + |d| := abs_sub _ _
    _ ≤ (|a+b|+|c|)+|d| := by gcongr; exact abs_sub _ _
    _ ≤ ((|a|+|b|)+|c|)+|d| := by gcongr; exact abs_add_le _ _
    _ ≤ _ := by dsimp [a, b, c, d]; nlinarith

def absoluteLp {A : Type*} [MeasurableSpace A] {μ : Measure A}
    (f : Lp ℝ 2 μ) : Lp ℝ 2 μ := (Lp.memLp f).norm.toLp (fun x => ‖f x‖)

theorem absoluteLp_ae {A : Type*} [MeasurableSpace A] {μ : Measure A}
    (f : Lp ℝ 2 μ) : absoluteLp f =ᵐ[μ] (fun x => ‖f x‖) := MemLp.coeFn_toLp _

theorem absoluteLp_norm {A : Type*} [MeasurableSpace A] {μ : Measure A}
    (f : Lp ℝ 2 μ) : ‖absoluteLp f‖ = ‖f‖ := by
  unfold absoluteLp
  rw [Lp.norm_toLp, eLpNorm_norm]
  rfl

def sumAbsoluteLegs {R : ℝ} (hR : 0 ≤ R) (f : H R) : J R :=
  absoluteLp (leg hR 0 f) + absoluteLp (leg hR 1 f) +
    absoluteLp (leg hR 2 f) + absoluteLp (leg hR 3 f)

theorem sumAbsoluteLegs_ae {R : ℝ} (hR : 0 ≤ R) (f : H R) :
    sumAbsoluteLegs hR f =ᵐ[pairingMeasure R]
      (fun k => |f (k 0)| + |f (k 1)| + |f (k 2)| + |f (k 3)|) := by
  let a := absoluteLp (leg hR 0 f)
  let b := absoluteLp (leg hR 1 f)
  let c := absoluteLp (leg hR 2 f)
  let d := absoluteLp (leg hR 3 f)
  filter_upwards [Lp.coeFn_add (a+b+c) d, Lp.coeFn_add (a+b) c, Lp.coeFn_add a b,
    absoluteLp_ae (leg hR 0 f), absoluteLp_ae (leg hR 1 f),
    absoluteLp_ae (leg hR 2 f), absoluteLp_ae (leg hR 3 f),
    leg_ae hR 0 f, leg_ae hR 1 f, leg_ae hR 2 f, leg_ae hR 3 f]
      with k ha hb hc h0 h1 h2 h3 l0 l1 l2 l3
  change (a+b+c+d) k = _
  simp only [Pi.add_apply] at ha hb hc
  rw [ha, hb, hc]
  change absoluteLp (leg hR 0 f) k + absoluteLp (leg hR 1 f) k +
    absoluteLp (leg hR 2 f) k + absoluteLp (leg hR 3 f) k = _
  rw [h0, h1, h2, h3, l0, l1, l2, l3]
  rfl

theorem sumAbsoluteLegs_bound {R : ℝ} (hR : 0 ≤ R) (f : H R) :
    ‖sumAbsoluteLegs hR f‖ ≤ 4 * inclusionNorm R * ‖f‖ := by
  calc
    ‖sumAbsoluteLegs hR f‖ ≤
        ‖absoluteLp (leg hR 0 f) + absoluteLp (leg hR 1 f) + absoluteLp (leg hR 2 f)‖ +
        ‖absoluteLp (leg hR 3 f)‖ := norm_add_le _ _
    _ ≤ ((‖absoluteLp (leg hR 0 f)‖ + ‖absoluteLp (leg hR 1 f)‖) +
        ‖absoluteLp (leg hR 2 f)‖) + ‖absoluteLp (leg hR 3 f)‖ := by
      gcongr
      calc
        _ ≤ ‖absoluteLp (leg hR 0 f) + absoluteLp (leg hR 1 f)‖ +
          ‖absoluteLp (leg hR 2 f)‖ := norm_add_le _ _
        _ ≤ _ := by gcongr; exact norm_add_le _ _
    _ ≤ _ := by
      simp only [absoluteLp_norm]
      linarith [leg_bound hR 0 f, leg_bound hR 1 f, leg_bound hR 2 f, leg_bound hR 3 f]

theorem jointPolynomial_lipschitz_on_amplitude {R B : ℝ} (hR : 0 ≤ R) (hB : 0 ≤ B)
    (f g : H R) (hf : MemLp f ∞ (physicalMeasure R)) (hg : MemLp g ∞ (physicalMeasure R))
    (hb : ∀ᵐ k ∂physicalMeasure R, |f k| ≤ B ∧ |g k| ≤ B) :
    ‖jointPolynomial hR f hf - jointPolynomial hR g hg‖ ≤
      12 * B ^ 2 * inclusionNorm R * ‖f-g‖ := by
  have hall : ∀ᵐ k ∂pairingMeasure R, ∀ i, |f (k i)| ≤ B ∧ |g (k i)| ≤ B :=
    ae_all_iff.mpr (fun i => (JointMultiplier.leg_quasiMeasurePreserving_cube R i).ae hb)
  have hsub : ∀ᵐ k ∂pairingMeasure R, ∀ i, (f-g) (k i) = f (k i)-g (k i) :=
    ae_all_iff.mpr (fun i => (JointMultiplier.leg_quasiMeasurePreserving_cube R i).ae_eq
      (Lp.coeFn_sub f g))
  have hpoint : ∀ᵐ k ∂pairingMeasure R,
      ‖(jointPolynomial hR f hf - jointPolynomial hR g hg) k‖ ≤
        (3 * B ^ 2) * ‖sumAbsoluteLegs hR (f-g) k‖ := by
    filter_upwards [hall, hsub, jointPolynomial_ae hR f hf, jointPolynomial_ae hR g hg,
      Lp.coeFn_sub (jointPolynomial hR f hf) (jointPolynomial hR g hg),
      sumAbsoluteLegs_ae hR (f-g)] with k hb hs hf' hg' hj hl
    simp only [Pi.sub_apply] at hj
    rw [hj, hf', hg', hl, hs 0, hs 1, hs 2, hs 3, Real.norm_eq_abs, Real.norm_eq_abs]
    have hsum : 0 ≤ |f (k 0)-g (k 0)| + |f (k 1)-g (k 1)| +
        |f (k 2)-g (k 2)| + |f (k 3)-g (k 3)| := by positivity
    rw [abs_of_nonneg hsum]
    exact cubic_difference_bound hB _ _ (fun i => (hb i).1) (fun i => (hb i).2)
  have hn := Lp.norm_le_mul_norm_of_ae_le_mul hpoint
  have hs := mul_le_mul_of_nonneg_left (sumAbsoluteLegs_bound hR (f-g))
    (by positivity : 0 ≤ 3 * B ^ 2)
  exact hn.trans (by nlinarith [hs])

theorem output_lipschitz_on_amplitude {R B : ℝ} (hR : 0 ≤ R) (hB : 0 ≤ B)
    (f g : H R) (hf : MemLp f ∞ (physicalMeasure R)) (hg : MemLp g ∞ (physicalMeasure R))
    (hb : ∀ᵐ k ∂physicalMeasure R, |f k| ≤ B ∧ |g k| ≤ B) :
    ‖output hR f hf - output hR g hg‖ ≤
      (‖(leg hR 0).adjoint‖ * (12 * B ^ 2 * inclusionNorm R)) * ‖f-g‖ := by
  rw [output, output, ← map_sub]
  exact ((leg hR 0).adjoint.le_opNorm _).trans (by
    have h := mul_le_mul_of_nonneg_left (jointPolynomial_lipschitz_on_amplitude hR hB f g hf hg hb)
      (norm_nonneg (leg hR 0).adjoint)
    nlinarith)

end
end Resonance.NonlinearContinuity
