import Resonance.ComplexLpDecomposition

/-! Complex scalar linearity of the actual real-imaginary L2 lift. -/
open MeasureTheory
namespace Resonance.ComplexLpLinear
noncomputable section
open ComplexLpDecomposition

theorem real_combination_ae {X : Type*} [MeasurableSpace X] {μ : Measure X}
    (a b : ℝ) (f g : Lp ℝ 2 μ) :
    (a • f+b • g : Lp ℝ 2 μ)=ᵐ[μ] (fun x=>a*f x+b*g x) := by
  filter_upwards [Lp.coeFn_add (a • f) (b • g),Lp.coeFn_smul a f,Lp.coeFn_smul b g]
    with x ha hf hg
  rw [ha]
  change (a • f) x+(b • g) x=_
  rw [hf,hg]
  rfl

theorem realPart_smul {X : Type*} [MeasurableSpace X] {μ : Measure X}
    (z : ℂ) (u : Lp ℂ 2 μ) :
    realPart μ (z • u)=z.re • realPart μ u+(-z.im) • imagPart μ u := by
  apply Lp.ext
  filter_upwards [realPart_ae (z • u),Lp.coeFn_smul z u,
    real_combination_ae z.re (-z.im) (realPart μ u) (imagPart μ u),
    realPart_ae u,imagPart_ae u] with x hz hs hc hr hi
  rw [hz,hc,hr,hi,hs]
  simp only [Pi.smul_apply,smul_eq_mul,Complex.mul_re]
  ring

theorem imagPart_smul {X : Type*} [MeasurableSpace X] {μ : Measure X}
    (z : ℂ) (u : Lp ℂ 2 μ) :
    imagPart μ (z • u)=z.im • realPart μ u+z.re • imagPart μ u := by
  apply Lp.ext
  filter_upwards [imagPart_ae (z • u),Lp.coeFn_smul z u,
    real_combination_ae z.im z.re (realPart μ u) (imagPart μ u),
    realPart_ae u,imagPart_ae u] with x hz hs hc hr hi
  rw [hz,hc,hr,hi,hs]
  simp only [Pi.smul_apply,smul_eq_mul,Complex.mul_im]
  ring

theorem parts_injective {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {u v : Lp ℂ 2 μ} (hr : realPart μ u=realPart μ v) (hi : imagPart μ u=imagPart μ v) : u=v := by
  apply Lp.ext
  have hru := realPart_ae u
  have hiu := imagPart_ae u
  rw [hr] at hru
  rw [hi] at hiu
  filter_upwards [hru,hiu,realPart_ae v,imagPart_ae v] with x h1 h2 h3 h4
  exact Complex.ext (h1.symm.trans h3) (h2.symm.trans h4)

theorem lift_smul {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {μ : Measure X} {ν : Measure Y} (T : Lp ℝ 2 μ→L[ℝ]Lp ℝ 2 ν)
    (z : ℂ) (u : Lp ℂ 2 μ) : lift T (z • u)=z • lift T u := by
  apply parts_injective
  · simp only [realPart_lift,realPart_smul,imagPart_lift,map_add,map_smul]
  · simp only [imagPart_lift,imagPart_smul,realPart_lift,map_add,map_smul]

def complexLift {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {μ : Measure X} {ν : Measure Y} (T : Lp ℝ 2 μ→L[ℝ]Lp ℝ 2 ν) :
    Lp ℂ 2 μ→L[ℂ]Lp ℂ 2 ν where
  toFun := lift T
  map_add' := (lift T).map_add
  map_smul' z u := lift_smul T z u
  cont := (lift T).continuous

theorem complexLift_apply {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {μ : Measure X} {ν : Measure Y} (T : Lp ℝ 2 μ→L[ℝ]Lp ℝ 2 ν)
    (u : Lp ℂ 2 μ) : complexLift T u=lift T u := rfl

theorem complexLift_zero_iff {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {μ : Measure X} {ν : Measure Y} (T : Lp ℝ 2 μ→L[ℝ]Lp ℝ 2 ν)
    (u : Lp ℂ 2 μ) : complexLift T u=0 ↔ T (realPart μ u)=0 ∧ T (imagPart μ u)=0 := by
  constructor
  · intro h
    change lift T u=0 at h
    constructor
    · rw [←realPart_lift,h,map_zero]
    · rw [←imagPart_lift,h,map_zero]
  · rintro ⟨hr,hi⟩
    apply parts_injective <;> simp only [complexLift_apply,realPart_lift,imagPart_lift,hr,hi,map_zero]

theorem lift_sub_norm_square {X : Type*} [MeasurableSpace X]
    {μ : Measure X} (P : Lp ℝ 2 μ→L[ℝ]Lp ℝ 2 μ)
    (u : Lp ℂ 2 μ) : ‖u-lift P u‖^2=
      ‖realPart μ u-P (realPart μ u)‖^2+‖imagPart μ u-P (imagPart μ u)‖^2 := by
  rw [norm_square_parts,map_sub,map_sub,realPart_lift,imagPart_lift]

end
end Resonance.ComplexLpLinear
