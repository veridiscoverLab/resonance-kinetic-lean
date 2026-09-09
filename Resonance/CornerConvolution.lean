import Resonance.AxisProductDensity

/-! The three-coordinate convolution of the actual sharp polygon
product laws.  All identities are nonnegative integrals, so no
totalized Bochner integral can erase a nonintegrable density. -/
open Real Set MeasureTheory
open scoped ENNReal Topology
namespace Resonance.CornerConvolution
noncomputable section
set_option maxHeartbeats 800000
open Resonance.CornerProductCoordinates Resonance.AxisProductDensity

def sumDensity (d:Fin 3→ℝ) (E:ℝ) : ℝ≥0∞ :=
  ∫⁻s:ℝ,∫⁻t:ℝ,axisDensity (d 0) s*axisDensity (d 1) t*
    axisDensity (d 2) (E-s-t)

theorem sumDensity_measurable (d:Fin 3→ℝ) : Measurable (sumDensity d) := by
  have h : Measurable (fun p:ℝ×(ℝ×ℝ)=>axisDensity (d 0) p.2.1*
      axisDensity (d 1) p.2.2*axisDensity (d 2) (p.1-p.2.1-p.2.2)) := by
    exact (((axisDensity_measurable _).comp measurable_snd.fst).mul
      ((axisDensity_measurable _).comp measurable_snd.snd)).mul
      ((axisDensity_measurable _).comp (by fun_prop))
  have h' : Measurable (fun p:(ℝ×ℝ)×ℝ=>axisDensity (d 0) p.1.2*
      axisDensity (d 1) p.2*axisDensity (d 2) (p.1.1-p.1.2-p.2)) :=
    h.comp (measurable_fst.fst.prodMk (measurable_fst.snd.prodMk measurable_snd))
  exact h'.lintegral_prod_right'.lintegral_prod_right'

theorem triple_density_sum (a b c F:ℝ→ℝ≥0∞)
    (ha:Measurable a) (hb:Measurable b) (hc:Measurable c) (hF:Measurable F) :
    (∫⁻s:ℝ,∫⁻t:ℝ,∫⁻u:ℝ,F (s+t+u)*a s*b t*c u)=
      ∫⁻E:ℝ,F E*(∫⁻s:ℝ,∫⁻t:ℝ,a s*b t*c (E-s-t)) := by
  have ht (s t:ℝ) :
      (∫⁻u:ℝ,F (s+t+u)*a s*b t*c u)=
        ∫⁻E:ℝ,F E*a s*b t*c (E-s-t) := by
    have he := lintegral_add_left_eq_self (μ:=(volume:Measure ℝ))
      (fun E:ℝ=>F E*a s*b t*c (E-s-t)) (s+t)
    have hcancel (x:ℝ) : s+t+x-s-t=x := by ring
    simpa only [hcancel] using he
  simp_rw [ht]
  have hm (s:ℝ) : Measurable (Function.uncurry
      (fun t E:ℝ=>F E*a s*b t*c (E-s-t))) := by fun_prop
  simp_rw [lintegral_lintegral_swap (hm _).aemeasurable]
  have hn : Measurable (fun p:ℝ×ℝ=>∫⁻t:ℝ,F p.2*a p.1*b t*c (p.2-p.1-t)) := by
    have hh : Measurable (fun p:(ℝ×ℝ)×ℝ=>
        F p.1.2*a p.1.1*b p.2*c (p.1.2-p.1.1-p.2)) := by fun_prop
    exact hh.lintegral_prod_right'
  rw [lintegral_lintegral_swap hn.aemeasurable]
  apply lintegral_congr
  intro E
  have hinner (s:ℝ) : Measurable (fun t:ℝ=>a s*b t*c (E-s-t)) := by fun_prop
  have houter : Measurable (fun s:ℝ=>∫⁻t:ℝ,a s*b t*c (E-s-t)) := by
    have hh : Measurable (fun p:ℝ×ℝ=>a p.1*b p.2*c (E-p.1-p.2)) := by fun_prop
    exact hh.lintegral_prod_right'
  rw [←lintegral_const_mul _ houter]
  apply lintegral_congr
  intro s
  rw [←lintegral_const_mul _ (hinner s)]
  apply lintegral_congr
  intro t
  ring

def polygonSource (d:Fin 3→ℝ) (F:ℝ→ℝ≥0∞) : ℝ≥0∞ :=
  ∫⁻p₀ in axisDomain (d 0),∫⁻p₁ in axisDomain (d 1),
    ∫⁻p₂ in axisDomain (d 2),
      F (p₀.1*p₀.2+p₁.1*p₁.2+p₂.1*p₂.2)
      ∂((volume:Measure ℝ).prod volume)
    ∂((volume:Measure ℝ).prod volume)
  ∂((volume:Measure ℝ).prod volume)

/-- All three actual polygons, with all their original flags, produce
the explicit sum density.  No sign configuration is removed. -/
theorem polygon_sum_density (d:Fin 3→ℝ)
    (hd0:∀i,0≤d i) (hd1:∀i,d i<1) (F:ℝ→ℝ≥0∞) (hF:Measurable F) :
    polygonSource d F=∫⁻E:ℝ,F E*sumDensity d E := by
  unfold polygonSource
  have h2 (s t:ℝ) := full_axis_product_lintegral (hd0 2) (hd1 2)
    (fun u=>F (s+t+u)) (by fun_prop)
  simp_rw [h2]
  have h1 (s:ℝ) : Measurable (fun t:ℝ=>∫⁻u:ℝ,F (s+t+u)*axisDensity (d 2) u) := by
    have hh : Measurable (fun p:ℝ×ℝ=>F (s+p.1+p.2)*axisDensity (d 2) p.2) :=
      (hF.comp (by fun_prop)).mul ((axisDensity_measurable _).comp measurable_snd)
    exact hh.lintegral_prod_right'
  have he1 (s:ℝ) := full_axis_product_lintegral (hd0 1) (hd1 1)
    (fun t=>∫⁻u:ℝ,F (s+t+u)*axisDensity (d 2) u) (h1 s)
  simp_rw [he1]
  have h0 : Measurable (fun s:ℝ=>∫⁻t:ℝ,
      (∫⁻u:ℝ,F (s+t+u)*axisDensity (d 2) u)*axisDensity (d 1) t) := by
    have hh : Measurable (fun p:(ℝ×ℝ)×ℝ=>
        F (p.1.1+p.1.2+p.2)*axisDensity (d 2) p.2) :=
      (hF.comp (by fun_prop)).mul ((axisDensity_measurable _).comp measurable_snd)
    exact (hh.lintegral_prod_right'.mul
      ((axisDensity_measurable _).comp measurable_snd)).lintegral_prod_right'
  rw [full_axis_product_lintegral (hd0 0) (hd1 0) _ h0]
  unfold sumDensity
  rw [←triple_density_sum (axisDensity (d 0)) (axisDensity (d 1)) (axisDensity (d 2)) F (axisDensity_measurable _)
    (axisDensity_measurable _) (axisDensity_measurable _) hF]
  apply lintegral_congr
  intro s
  have hm : Measurable (fun t:ℝ=>
      (∫⁻u:ℝ,F (s+t+u)*axisDensity (d 2) u)*axisDensity (d 1) t) :=
    (h1 s).mul (axisDensity_measurable _)
  rw [←lintegral_mul_const _ hm]
  apply lintegral_congr
  intro t
  have hh : Measurable (fun u:ℝ=>F (s+t+u)*axisDensity (d 2) u) := by
    exact (hF.comp (by fun_prop)).mul (axisDensity_measurable _)
  rw [←lintegral_mul_const _ hh,←lintegral_mul_const _ (hh.mul measurable_const)]
  apply lintegral_congr
  intro u
  ring

end
end Resonance.CornerConvolution
