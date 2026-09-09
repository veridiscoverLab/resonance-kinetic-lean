import Resonance.PhysicalMicroCoercivity

/-! Actual real and imaginary L2 representatives, their Pythagoras identity,
and complexification of an arbitrary proved real bounded operator. -/
open MeasureTheory
namespace Resonance.ComplexLpDecomposition
noncomputable section

def realPart {X : Type*} [MeasurableSpace X] (μ : Measure X) :
    Lp ℂ 2 μ→L[ℝ]Lp ℝ 2 μ := Complex.reCLM.compLpL 2 μ

def imagPart {X : Type*} [MeasurableSpace X] (μ : Measure X) :
    Lp ℂ 2 μ→L[ℝ]Lp ℝ 2 μ := Complex.imCLM.compLpL 2 μ

def realEmbed {X : Type*} [MeasurableSpace X] (μ : Measure X) :
    Lp ℝ 2 μ→L[ℝ]Lp ℂ 2 μ := Complex.ofRealCLM.compLpL 2 μ

theorem realPart_ae {X : Type*} [MeasurableSpace X] {μ : Measure X} (u : Lp ℂ 2 μ) :
    (realPart μ u : X→ℝ)=ᵐ[μ] (fun x=>(u x).re) := Complex.reCLM.coeFn_compLpL u

theorem imagPart_ae {X : Type*} [MeasurableSpace X] {μ : Measure X} (u : Lp ℂ 2 μ) :
    (imagPart μ u : X→ℝ)=ᵐ[μ] (fun x=>(u x).im) := Complex.imCLM.coeFn_compLpL u

theorem realEmbed_ae {X : Type*} [MeasurableSpace X] {μ : Measure X} (u : Lp ℝ 2 μ) :
    (realEmbed μ u : X→ℂ)=ᵐ[μ] (fun x=>(u x : ℂ)) := Complex.ofRealCLM.coeFn_compLpL u

theorem norm_square_integral {X E : Type*} [MeasurableSpace X] {μ : Measure X}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] (u : Lp E 2 μ) :
    ‖u‖^2=∫x,‖u x‖^2∂μ := by
  rw [←real_inner_self_eq_norm_sq,L2.inner_def]
  apply integral_congr_ae
  exact ae_of_all _ (fun x=>real_inner_self_eq_norm_sq (u x))

theorem norm_square_integrable {X E : Type*} [MeasurableSpace X] {μ : Measure X}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] (u : Lp E 2 μ) :
    Integrable (fun x=>‖u x‖^2) μ := by
  apply (L2.integrable_inner (𝕜:=ℝ) u u).congr
  exact ae_of_all _ (fun x=>real_inner_self_eq_norm_sq (u x))

theorem norm_square_parts {X : Type*} [MeasurableSpace X] {μ : Measure X} (u : Lp ℂ 2 μ) :
    ‖u‖^2=‖realPart μ u‖^2+‖imagPart μ u‖^2 := by
  rw [norm_square_integral u,norm_square_integral (realPart μ u),
    norm_square_integral (imagPart μ u),←integral_add
      (norm_square_integrable (realPart μ u)) (norm_square_integrable (imagPart μ u))]
  apply integral_congr_ae
  filter_upwards [realPart_ae u,imagPart_ae u] with x hr hi
  rw [hr,hi,Complex.sq_norm,Complex.normSq_apply]
  simp only [Real.norm_eq_abs,sq_abs]
  ring

def lift {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {μ : Measure X} {ν : Measure Y} (T : Lp ℝ 2 μ→L[ℝ]Lp ℝ 2 ν) :
    Lp ℂ 2 μ→L[ℝ]Lp ℂ 2 ν :=
  ((realEmbed ν).comp T).comp (realPart μ)+
    Complex.I • (((realEmbed ν).comp T).comp (imagPart μ))

theorem lift_ae {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {μ : Measure X} {ν : Measure Y} (T : Lp ℝ 2 μ→L[ℝ]Lp ℝ 2 ν) (u : Lp ℂ 2 μ) :
    (lift T u : Y→ℂ)=ᵐ[ν]
      (fun y=>(T (realPart μ u) y : ℂ)+Complex.I*(T (imagPart μ u) y : ℂ)) := by
  change (realEmbed ν (T (realPart μ u))+Complex.I • realEmbed ν (T (imagPart μ u)) : Lp ℂ 2 ν)=ᵐ[ν] _
  filter_upwards [Lp.coeFn_add (realEmbed ν (T (realPart μ u)))
    (Complex.I • realEmbed ν (T (imagPart μ u))),
    Lp.coeFn_smul Complex.I (realEmbed ν (T (imagPart μ u))),
    realEmbed_ae (T (realPart μ u)),realEmbed_ae (T (imagPart μ u))] with y ha hs hr hi
  rw [ha]
  change realEmbed ν (T (realPart μ u)) y+(Complex.I • realEmbed ν (T (imagPart μ u))) y=_
  rw [hs]
  simp only [Pi.smul_apply,smul_eq_mul,hr,hi]

theorem realPart_lift {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {μ : Measure X} {ν : Measure Y} (T : Lp ℝ 2 μ→L[ℝ]Lp ℝ 2 ν) (u : Lp ℂ 2 μ) :
    realPart ν (lift T u)=T (realPart μ u) := by
  apply Lp.ext
  filter_upwards [realPart_ae (lift T u),lift_ae T u] with y hr hl
  rw [hr,hl]
  simp

theorem imagPart_lift {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {μ : Measure X} {ν : Measure Y} (T : Lp ℝ 2 μ→L[ℝ]Lp ℝ 2 ν) (u : Lp ℂ 2 μ) :
    imagPart ν (lift T u)=T (imagPart μ u) := by
  apply Lp.ext
  filter_upwards [imagPart_ae (lift T u),lift_ae T u] with y hr hl
  rw [hr,hl]
  simp

theorem lift_norm_square {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {μ : Measure X} {ν : Measure Y} (T : Lp ℝ 2 μ→L[ℝ]Lp ℝ 2 ν) (u : Lp ℂ 2 μ) :
    ‖lift T u‖^2=‖T (realPart μ u)‖^2+‖T (imagPart μ u)‖^2 := by
  rw [norm_square_parts,realPart_lift,imagPart_lift]

end
end Resonance.ComplexLpDecomposition
