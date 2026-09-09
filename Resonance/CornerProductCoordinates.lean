import Resonance.CollisionFrequencyPositive
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! Actual one-coordinate product change of variables for the sharp
cube.  No frequency asymptotic or convolution identity is assumed. -/
open Real Set MeasureTheory
open scoped ENNReal Topology
namespace Resonance.CornerProductCoordinates
noncomputable section
set_option maxHeartbeats 600000

/-- The exact rescaled three-flag polygon in one coordinate. -/
def axisDomain (d:ℝ) : Set (ℝ×ℝ) :=
  {p | p.1∈Icc (-1+d) d ∧ p.2∈Icc (-1+d) d ∧ p.1+p.2∈Icc (-1+d) d}

theorem axisDomain_mixed {d x y:ℝ} (hd0:0≤d) (hd1:d≤1)
    (hx:0≤x) (hy:0≤y) :
    (x,-y)∈axisDomain d ↔ x≤d ∧ y≤1-d := by
  dsimp [axisDomain]
  constructor
  · intro h
    exact ⟨h.1.2,by linarith [h.2.1.1]⟩
  · rintro ⟨hxd,hyd⟩
    constructor
    · constructor <;> linarith
    constructor <;> constructor <;> linarith

theorem axisDomain_positive {d x y:ℝ} (hd1:d≤1)
    (hx:0≤x) (hy:0≤y) :
    (x,y)∈axisDomain d ↔ x+y≤d := by
  dsimp [axisDomain]
  constructor
  · exact fun h=>h.2.2.2
  · intro h
    constructor
    · constructor <;> linarith
    constructor <;> constructor <;> linarith

theorem axisDomain_negative {d x y:ℝ} (hd0:0≤d)
    (hx:0≤x) (hy:0≤y) :
    (-x,-y)∈axisDomain d ↔ x+y≤1-d := by
  dsimp [axisDomain]
  constructor
  · intro h
    linarith [h.2.2.1]
  · intro h
    constructor
    · constructor <;> linarith
    constructor <;> constructor <;> linarith

/-- The actual Jacobian for (x,y) ↦ (x,xy), x>0.  The nonnegative
integral formulation permits every measurable test, including infinite
integrals, with no Bochner-totalization issue. -/
theorem product_coordinate_lintegral (F:ℝ×ℝ→ℝ≥0∞) (hF:Measurable F) :
    (∫⁻x in Ioi (0:ℝ),∫⁻y:ℝ,F (x,x*y)) =
      ∫⁻x in Ioi (0:ℝ),∫⁻t:ℝ,ENNReal.ofReal (x⁻¹)*F (x,t) := by
  apply lintegral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  have hm : Measurable (fun t:ℝ=>F (x,t)) := hF.comp measurable_prodMk_left
  calc
    _ = ∫⁻t:ℝ,F (x,t) ∂Measure.map (fun y:ℝ=>x*y) volume :=
      (lintegral_map hm (measurable_const_mul x)).symm
    _ = _ := by
      rw [Real.map_volume_mul_left (ne_of_gt hx),lintegral_smul_measure,
        abs_of_pos (inv_pos.mpr hx),smul_eq_mul,←lintegral_const_mul _ hm]

theorem mixed_product_section {a b t x:ℝ} (hb:0<b) (hx:0<x) :
    (x≤a ∧ t/x≤b) ↔ x∈Icc (t/b) a := by
  have h : t/x≤b ↔ t/b≤x := by
    rw [div_le_iff₀ hx,div_le_iff₀ hb]
    rw [mul_comm b x]
  simp only [mem_Icc,h,and_comm]

/-- One mixed quadrant gives the exact logarithmic product Jacobian.
The second quadrant has the same value by interchange of the two axes. -/
theorem mixed_product_jacobian {a b t:ℝ} (ha:0<a) (hb:0<b)
    (ht:0<t) (htop:t<a*b) :
    (∫x in Icc (t/b) a,(x:ℝ)⁻¹)=Real.log (a*b/t) := by
  have hlo : 0<t/b := div_pos ht hb
  have hle : t/b≤a := (div_le_iff₀ hb).mpr htop.le
  rw [integral_Icc_eq_integral_Ioc,←intervalIntegral.integral_of_le hle,
    integral_inv_of_pos hlo ha]
  congr 1
  field_simp

def lowerRoot (b t:ℝ) : ℝ := (b-Real.sqrt (b^2-4*t))/2
def upperRoot (b t:ℝ) : ℝ := (b+Real.sqrt (b^2-4*t))/2

theorem product_roots {b t:ℝ} (hb:0<b) (ht:0<t) (htop:t<b^2/4) :
    0<lowerRoot b t ∧ lowerRoot b t<upperRoot b t ∧
      lowerRoot b t+upperRoot b t=b ∧ lowerRoot b t*upperRoot b t=t := by
  have hd : 0<b^2-4*t := by linarith
  have hs := Real.sq_sqrt hd.le
  have hs0 := Real.sqrt_pos.mpr hd
  have hsb : Real.sqrt (b^2-4*t)<b := by nlinarith
  dsimp [lowerRoot,upperRoot]
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · ring
  · nlinarith

theorem positive_product_section {b t x:ℝ} (hb:0<b) (ht:0<t)
    (htop:t<b^2/4) (hx:0<x) :
    x+t/x≤b ↔ x∈Icc (lowerRoot b t) (upperRoot b t) := by
  obtain ⟨hl,hlu,hs,hp⟩ := product_roots hb ht htop
  have hpol : x+t/x≤b ↔ x^2-b*x+t≤0 := by
    rw [←mul_le_mul_iff_right₀ hx]
    field_simp
    constructor <;> intro h <;> nlinarith
  rw [hpol,mem_Icc]
  have hf : x^2-b*x+t=(x-lowerRoot b t)*(x-upperRoot b t) := by
    calc
      _ = x^2-(lowerRoot b t+upperRoot b t)*x+lowerRoot b t*upperRoot b t := by rw [hs,hp]
      _ = _ := by ring
  rw [hf,mul_nonpos_iff]
  constructor
  · rintro (h|h)
    · constructor <;> linarith [h.1,h.2]
    · exfalso
      linarith [h.1,h.2]
  · rintro ⟨h1,h2⟩
    exact Or.inl ⟨by linarith,by linarith⟩

/-- The actual same-sign triangle has the square-root logarithmic
Jacobian appearing in the paper's positive product density. -/
theorem positive_product_jacobian {b t:ℝ} (hb:0<b) (ht:0<t)
    (htop:t<b^2/4) :
    (∫x in Icc (lowerRoot b t) (upperRoot b t),(x:ℝ)⁻¹)=
      Real.log ((b+Real.sqrt (b^2-4*t))^2/(4*t)) := by
  obtain ⟨hl,hlu,hs,hp⟩ := product_roots hb ht htop
  rw [integral_Icc_eq_integral_Ioc,←intervalIntegral.integral_of_le hlu.le,
    integral_inv_of_pos hl (hl.trans hlu)]
  congr 1
  calc
    upperRoot b t / lowerRoot b t = (upperRoot b t)^2/t := by
      apply (div_eq_div_iff hl.ne' ht.ne').mpr
      nlinarith [congrArg (fun z:ℝ=>upperRoot b t*z) hp]
    _ = _ := by dsimp [upperRoot]; ring

end
end Resonance.CornerProductCoordinates
