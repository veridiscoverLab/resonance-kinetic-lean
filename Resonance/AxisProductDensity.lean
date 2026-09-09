import Resonance.TriangleProductDensity
import Mathlib.MeasureTheory.Group.LIntegral

open Real Set MeasureTheory
open scoped ENNReal Topology
namespace Resonance.AxisProductDensity
noncomputable section
set_option maxHeartbeats 600000
open Resonance.CornerProductCoordinates Resonance.CornerProductDensity
open Resonance.TriangleProductDensity

theorem positive_negative_lintegral (F:ℝ→ℝ≥0∞) (_hF:Measurable F) :
    (∫⁻x:ℝ,F x)=(∫⁻x in Ioi (0:ℝ),F x)+(∫⁻x in Ioi (0:ℝ),F (-x)) := by
  have hn : (∫⁻x in Ioi (0:ℝ),F (-x))=∫⁻x in Iio (0:ℝ),F x := by
    rw [←lintegral_indicator measurableSet_Ioi,←lintegral_indicator measurableSet_Iio]
    have he : (fun x:ℝ=>(Ioi (0:ℝ)).indicator (fun x=>F (-x)) x)=
        fun x:ℝ=>(Iio (0:ℝ)).indicator F (-x) := by
      funext x
      simp only [Set.indicator_apply,mem_Ioi,mem_Iio,neg_lt_zero]
    rw [he]
    exact lintegral_neg_eq_self _
  rw [hn,Measure.restrict_congr_set (Iio_ae_eq_Iic (μ:=volume)),
    ←lintegral_add_compl F (measurableSet_Ioi (a:=(0:ℝ)))]
  simp only [compl_Ioi]

theorem closed_rectangle_lintegral (a b:ℝ) (F:ℝ×ℝ→ℝ≥0∞) :
    (∫⁻x in Ioi (0:ℝ),∫⁻y in Ioi (0:ℝ),
      if x≤a ∧ y≤b then F (x,y) else 0)=
      ∫⁻x in Ioo 0 a,∫⁻y in Ioo 0 b,F (x,y) := by
  have hsplit (c:ℝ) (G:ℝ→ℝ≥0∞) :
      (∫⁻x in Ioi (0:ℝ),if x≤c then G x else 0)=∫⁻x in Ioo 0 c,G x := by
    have hs : Iic c∩Ioi (0:ℝ)=Ioc 0 c := by ext x; simp [and_comm]
    change (∫⁻x in Ioi (0:ℝ),(Iic c).indicator G x)=_
    rw [lintegral_indicator measurableSet_Iic,Measure.restrict_restrict measurableSet_Iic,hs]
    exact setLIntegral_congr (Ioo_ae_eq_Ioc (μ:=volume)).symm
  have he (x:ℝ) : (∫⁻y in Ioi (0:ℝ),if x≤a ∧ y≤b then F (x,y) else 0)=
      if x≤a then ∫⁻y in Ioo 0 b,F (x,y) else 0 := by
    by_cases hx:x≤a
    · simp only [hx,true_and,if_true]
      exact hsplit b (fun y=>F (x,y))
    · simp [hx]
  simp_rw [he]
  exact hsplit a _

theorem axisDomain_measurable (d:ℝ) : MeasurableSet (axisDomain d) := by
  exact ((measurable_fst measurableSet_Icc).inter
    ((measurable_snd measurableSet_Icc).inter
      ((measurable_fst.add measurable_snd) measurableSet_Icc)))

theorem positive_quadrant_density {d:ℝ} (hd0:0≤d) (hd1:d≤1)
    (F:ℝ→ℝ≥0∞) (hF:Measurable F) :
    (∫⁻x in Ioi (0:ℝ),∫⁻y in Ioi (0:ℝ),
      (axisDomain d).indicator (fun p=>F (p.1*p.2)) (x,y))=
      ∫⁻t:ℝ,F t*triangleDensity d t := by
  classical
  rw [←triangle_product_density_nonnegative hd0 F hF]
  apply lintegral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  apply lintegral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
  change (if (x,y)∈axisDomain d then F (x*y) else 0)=_
  rw [axisDomain_positive hd1 (le_of_lt hx) (le_of_lt hy)]

theorem negative_quadrant_density {d:ℝ} (hd0:0≤d) (hd1:d≤1)
    (F:ℝ→ℝ≥0∞) (hF:Measurable F) :
    (∫⁻x in Ioi (0:ℝ),∫⁻y in Ioi (0:ℝ),
      (axisDomain d).indicator (fun p=>F (p.1*p.2)) (-x,-y))=
      ∫⁻t:ℝ,F t*triangleDensity (1-d) t := by
  classical
  rw [←triangle_product_density_nonnegative (sub_nonneg.mpr hd1) F hF]
  apply lintegral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  apply lintegral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
  change (if (-x,-y)∈axisDomain d then F ((-x)*(-y)) else 0)=_
  rw [axisDomain_negative hd0 (le_of_lt hx) (le_of_lt hy),neg_mul_neg]

theorem mixed_quadrant_density {d:ℝ} (hd0:0≤d) (hd1:d<1)
    (F:ℝ→ℝ≥0∞) (hF:Measurable F) :
    (∫⁻x in Ioi (0:ℝ),∫⁻y in Ioi (0:ℝ),
      (axisDomain d).indicator (fun p=>F (p.1*p.2)) (x,-y))=
      ∫⁻t:ℝ,F (-t)*rectangleDensity d (1-d) t := by
  classical
  rw [←rectangle_product_density (sub_pos.mpr hd1) (fun t=>F (-t)) (by fun_prop),
    ←closed_rectangle_lintegral d (1-d) (fun p=>F (-(p.1*p.2)))]
  apply lintegral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  apply lintegral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
  change (if (x,-y)∈axisDomain d then F (x*(-y)) else 0)=_
  rw [axisDomain_mixed hd0 hd1.le (le_of_lt hx) (le_of_lt hy),mul_neg]
  by_cases h:x≤d ∧ y≤1-d <;> simp [h]

theorem axisDomain_swap (d x y:ℝ) : (x,y)∈axisDomain d ↔ (y,x)∈axisDomain d := by
  simp [axisDomain,add_comm,and_left_comm]

theorem reversed_mixed_quadrant {d:ℝ} (F:ℝ→ℝ≥0∞) (hF:Measurable F) :
    (∫⁻x in Ioi (0:ℝ),∫⁻y in Ioi (0:ℝ),
      (axisDomain d).indicator (fun p=>F (p.1*p.2)) (-x,y))=
    (∫⁻x in Ioi (0:ℝ),∫⁻y in Ioi (0:ℝ),
      (axisDomain d).indicator (fun p=>F (p.1*p.2)) (x,-y)) := by
  classical
  have hG : Measurable ((axisDomain d).indicator (fun p:ℝ×ℝ=>F (p.1*p.2))) :=
    (hF.comp (measurable_fst.mul measurable_snd)).indicator (axisDomain_measurable d)
  have hh : Measurable (Function.uncurry (fun x y:ℝ=>
      (axisDomain d).indicator (fun p=>F (p.1*p.2)) (-x,y))) := by
    exact hG.comp (measurable_fst.neg.prodMk measurable_snd)
  rw [lintegral_lintegral_swap hh.aemeasurable]
  apply lintegral_congr
  intro x
  apply lintegral_congr
  intro y
  change (if (-y,x)∈axisDomain d then F ((-y)*x) else 0)=
    (if (x,-y)∈axisDomain d then F (x*(-y)) else 0)
  rw [axisDomain_swap d (-y) x,mul_comm (-y) x]

theorem full_quadrant_decomposition (G:ℝ×ℝ→ℝ≥0∞) (hG:Measurable G) :
    (∫⁻x:ℝ,∫⁻y:ℝ,G (x,y))=
    ((∫⁻x in Ioi (0:ℝ),∫⁻y in Ioi (0:ℝ),G (x,y))+
      (∫⁻x in Ioi (0:ℝ),∫⁻y in Ioi (0:ℝ),G (x,-y)))+
    ((∫⁻x in Ioi (0:ℝ),∫⁻y in Ioi (0:ℝ),G (-x,y))+
      (∫⁻x in Ioi (0:ℝ),∫⁻y in Ioi (0:ℝ),G (-x,-y))) := by
  have hout : Measurable (fun x:ℝ=>∫⁻y:ℝ,G (x,y)) := hG.lintegral_prod_right'
  rw [positive_negative_lintegral _ hout]
  have he (x:ℝ) : (∫⁻y:ℝ,G (x,y))=
      (∫⁻y in Ioi (0:ℝ),G (x,y))+(∫⁻y in Ioi (0:ℝ),G (x,-y)) :=
    positive_negative_lintegral _ (hG.comp measurable_prodMk_left)
  simp_rw [he]
  have hp : Measurable (fun x:ℝ=>∫⁻y in Ioi (0:ℝ),G (x,y)) := hG.lintegral_prod_right'
  have hpn : Measurable (fun x:ℝ=>∫⁻y in Ioi (0:ℝ),G (-x,y)) :=
    hp.comp measurable_neg
  rw [lintegral_add_left hp,lintegral_add_left hpn]

/-- The exact complete three-flag polygon product law, including all
four quadrants and d=0.  No axis atoms are added. -/
theorem full_axis_product_density {d:ℝ} (hd0:0≤d) (hd1:d<1)
    (F:ℝ→ℝ≥0∞) (hF:Measurable F) :
    (∫⁻p in axisDomain d,F (p.1*p.2) ∂((volume:Measure ℝ).prod volume))=
      (∫⁻t:ℝ,F t*triangleDensity d t)+
      (∫⁻t:ℝ,F t*triangleDensity (1-d) t)+
      2*(∫⁻t:ℝ,F (-t)*rectangleDensity d (1-d) t) := by
  let G : ℝ×ℝ→ℝ≥0∞ := (axisDomain d).indicator (fun p=>F (p.1*p.2))
  have hG : Measurable G :=
    (hF.comp (measurable_fst.mul measurable_snd)).indicator (axisDomain_measurable d)
  rw [←lintegral_indicator (axisDomain_measurable d),lintegral_prod _ hG.aemeasurable,
    full_quadrant_decomposition _ hG]
  dsimp only [G]
  rw [positive_quadrant_density hd0 hd1.le F hF,
    negative_quadrant_density hd0 hd1.le F hF,
    reversed_mixed_quadrant F hF,mixed_quadrant_density hd0 hd1 F hF]
  ring

theorem triangleDensity_measurable (b:ℝ) : Measurable (triangleDensity b) := by
  apply Measurable.ite
  · exact (measurableSet_lt measurable_const measurable_id).inter
      (measurableSet_lt measurable_id measurable_const)
  · fun_prop
  · exact measurable_const

theorem rectangleDensity_measurable (a b:ℝ) : Measurable (rectangleDensity a b) := by
  apply Measurable.ite
  · exact (measurableSet_lt measurable_const measurable_id).inter
      (measurableSet_lt measurable_id measurable_const)
  · fun_prop
  · exact measurable_const

def axisDensity (d t:ℝ) : ℝ≥0∞ := triangleDensity d t+triangleDensity (1-d) t+
  2*rectangleDensity d (1-d) (-t)

theorem axisDensity_measurable (d:ℝ) : Measurable (axisDensity d) :=
  ((triangleDensity_measurable d).add (triangleDensity_measurable (1-d))).add
    (measurable_const.mul ((rectangleDensity_measurable d (1-d)).comp measurable_neg))

theorem full_axis_product_lintegral {d:ℝ} (hd0:0≤d) (hd1:d<1)
    (F:ℝ→ℝ≥0∞) (hF:Measurable F) :
    (∫⁻p in axisDomain d,F (p.1*p.2) ∂((volume:Measure ℝ).prod volume))=
      ∫⁻t:ℝ,F t*axisDensity d t := by
  rw [full_axis_product_density hd0 hd1 F hF]
  have hn : (∫⁻t:ℝ,F (-t)*rectangleDensity d (1-d) t)=
      ∫⁻t:ℝ,F t*rectangleDensity d (1-d) (-t) := by
    simpa only [neg_neg] using lintegral_neg_eq_self
      (fun t:ℝ=>F t*rectangleDensity d (1-d) (-t))
  rw [hn]
  symm
  calc
    _ = ∫⁻t:ℝ,(F t*triangleDensity d t+F t*triangleDensity (1-d) t)+
        2*(F t*rectangleDensity d (1-d) (-t)) := by
      apply lintegral_congr
      intro t
      dsimp [axisDensity]
      ring
    _ = _ := by
      have h1 := hF.mul (triangleDensity_measurable d)
      have h2 := hF.mul (triangleDensity_measurable (1-d))
      have h3 : Measurable (fun t:ℝ=>F t*rectangleDensity d (1-d) (-t)) :=
        hF.mul ((rectangleDensity_measurable d (1-d)).comp measurable_neg)
      rw [lintegral_add_left (h1.add h2),lintegral_add_left h1,lintegral_const_mul _ h3]

def axisProductMeasure (d:ℝ) : Measure ℝ :=
  Measure.map (fun p:ℝ×ℝ=>p.1*p.2)
    (((volume:Measure ℝ).prod volume).restrict (axisDomain d))

/-- Equality of the actual complete polygon pushforward with the
explicit signed product density, not just an asserted scalar profile. -/
theorem axisProductMeasure_eq_withDensity {d:ℝ} (hd0:0≤d) (hd1:d<1) :
    axisProductMeasure d=(volume:Measure ℝ).withDensity (axisDensity d) := by
  classical
  apply Measure.ext
  intro s hs
  rw [axisProductMeasure,Measure.map_apply (measurable_fst.mul measurable_snd) hs,
    withDensity_apply _ hs]
  have h := full_axis_product_lintegral hd0 hd1 (s.indicator (fun _=>1))
    (measurable_const.indicator hs)
  have hl : (∫⁻p in axisDomain d,(s.indicator (fun _=>1)) (p.1*p.2)
      ∂((volume:Measure ℝ).prod volume))=
      (((volume:Measure ℝ).prod volume).restrict (axisDomain d))
        ((fun p:ℝ×ℝ=>p.1*p.2)⁻¹'s) := by
    rw [←lintegral_indicator_one ((measurable_fst.mul measurable_snd) hs)]
    apply lintegral_congr
    intro p
    by_cases hp:p.1*p.2∈s <;> simp [hp]
  have hr : (∫⁻t:ℝ,s.indicator (fun _=>1) t*axisDensity d t)=
      ∫⁻t in s,axisDensity d t := by
    rw [←lintegral_indicator hs]
    apply lintegral_congr
    intro t
    by_cases ht:t∈s <;> simp [Set.indicator_of_mem,Set.indicator_of_notMem,ht]
  rwa [hl,hr] at h

theorem axisProductMeasure_absolutelyContinuous {d:ℝ} (hd0:0≤d) (hd1:d<1) :
    axisProductMeasure d≪(volume:Measure ℝ) := by
  rw [axisProductMeasure_eq_withDensity hd0 hd1]
  exact withDensity_absolutelyContinuous _ _

end
end Resonance.AxisProductDensity
