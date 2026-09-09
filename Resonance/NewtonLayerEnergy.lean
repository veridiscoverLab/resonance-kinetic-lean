import Resonance.NewtonKernelBalls

/-! A self-contained Newton energy estimate for a countable family of
actual measurable layers.  All spatial input is a proved volume bound;
the singular kernel row is integrated by Euclidean polar coordinates. -/
open Real Set MeasureTheory
open scoped ENNReal Topology
namespace Resonance.NewtonLayerEnergy
noncomputable section
set_option maxHeartbeats 1000000
open Resonance.ResonantMeasure Resonance.NewtonKernelBalls

def sphereArea : ℝ := (surface univ).toReal

theorem sphereArea_nonnegative : 0 ≤ sphereArea := ENNReal.toReal_nonneg

theorem ofReal_sphereArea : ENNReal.ofReal sphereArea=surface univ :=
  ENNReal.ofReal_toReal (measure_ne_top _ _)

theorem kernelTwo_set_bound_real {r C:ℝ} (hr:0<r) (hC:0≤C) (S:Set E)
    (hS:MeasurableSet S) (hvol:volume S≤ENNReal.ofReal (C*r^3)) (k:E) :
    (∫⁻p in S,kernelTwo (k-p)) ≤ ENNReal.ofReal ((sphereArea+C)*r) := by
  have h := kernelTwo_set_bound hr hC S hS hvol k
  rw [←ofReal_sphereArea,←ENNReal.ofReal_add sphereArea_nonnegative hC,
    ←ENNReal.ofReal_mul (add_nonneg sphereArea_nonnegative hC)] at h
  exact h

def pairEnergy (w:E→ℝ≥0∞) (S T:Set E) : ℝ≥0∞ :=
  ∫⁻k in S,∫⁻p in T,w k*w p*kernelTwo (k-p)

theorem pairEnergy_symm {w:E→ℝ≥0∞} (hw:Measurable w) (S T:Set E) :
    pairEnergy w S T=pairEnergy w T S := by
  unfold pairEnergy
  rw [lintegral_lintegral_swap]
  · apply lintegral_congr
    intro p
    apply lintegral_congr
    intro k
    simp only [kernelTwo,norm_sub_rev]
    ring
  · exact ((hw.comp measurable_fst).mul (hw.comp measurable_snd)).mul
      (kernelTwo_measurable.comp (measurable_fst.sub measurable_snd)) |>.aemeasurable

theorem pairEnergy_bounded {w:E→ℝ≥0∞} {S T:Set E}
    (hS:MeasurableSet S) (hT:MeasurableSet T) {r s C a b:ℝ}
    (_hr:0<r) (hs:0<s) (hC:0≤C) (ha:0≤a) (hb:0≤b)
    (hVS:volume S≤ENNReal.ofReal (C*r^3))
    (hVT:volume T≤ENNReal.ofReal (C*s^3))
    (hwS:∀k∈S,w k≤ENNReal.ofReal a) (hwT:∀k∈T,w k≤ENNReal.ofReal b) :
    pairEnergy w S T ≤ ENNReal.ofReal (a*b*(sphereArea+C)*s*C*r^3) := by
  have harea := sphereArea_nonnegative
  have hrow (k:E) (hk:k∈S) :
      (∫⁻p in T,w k*w p*kernelTwo (k-p)) ≤
        ENNReal.ofReal (a*b*(sphereArea+C)*s) := by
    calc
      _ ≤ ∫⁻p in T,(ENNReal.ofReal a*ENNReal.ofReal b)*kernelTwo (k-p) := by
        apply lintegral_mono_ae
        filter_upwards [ae_restrict_mem hT] with p hp
        exact mul_le_mul_left (mul_le_mul (hwS k hk) (hwT p hp) (zero_le _) (zero_le _)) _
      _ = (ENNReal.ofReal a*ENNReal.ofReal b)*(∫⁻p in T,kernelTwo (k-p)) := by
        exact lintegral_const_mul _ (show Measurable (fun p:E=>kernelTwo (k-p)) from
          kernelTwo_measurable.comp (measurable_const.sub measurable_id))
      _ ≤ (ENNReal.ofReal a*ENNReal.ofReal b)*ENNReal.ofReal ((sphereArea+C)*s) :=
        mul_le_mul_right (kernelTwo_set_bound_real hs hC T hT hVT k) _
      _ = _ := by
        rw [←ENNReal.ofReal_mul ha,←ENNReal.ofReal_mul (mul_nonneg ha hb)]
        congr 1
        ring
  calc
    _ ≤ ∫⁻k in S,ENNReal.ofReal (a*b*(sphereArea+C)*s) := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem hS] with k hk
      exact hrow k hk
    _ = ENNReal.ofReal (a*b*(sphereArea+C)*s)*volume S := by
      rw [lintegral_const,Measure.restrict_apply_univ]
    _ ≤ ENNReal.ofReal (a*b*(sphereArea+C)*s)*ENNReal.ofReal (C*r^3) :=
      mul_le_mul_right hVS _
    _ = _ := by
      rw [←ENNReal.ofReal_mul (by positivity)]
      congr 1
      ring

/-- For the smaller outer layer, both inverse-square amplitudes cancel
against the actual cubic volume and the polar row. -/
theorem pairEnergy_scaled {w:E→ℝ≥0∞} {S T:Set E}
    (hS:MeasurableSet S) (hT:MeasurableSet T) {r s C A b d:ℝ}
    (hr:0<r) (hs:0<s) (hrs:r ≤ s) (hC:0≤C) (hA:0≤A) (hb:0≤b) (hd:0≤d)
    (hVS:volume S≤ENNReal.ofReal (C*r^3))
    (hVT:volume T≤ENNReal.ofReal (C*s^3))
    (hwS:∀k∈S,w k≤ENNReal.ofReal (A*b/r^2))
    (hwT:∀k∈T,w k≤ENNReal.ofReal (A*d/s^2)) :
    pairEnergy w S T ≤ ENNReal.ofReal (A^2*C*(sphereArea+C)*b*d) := by
  have harea := sphereArea_nonnegative
  apply (pairEnergy_bounded hS hT hr hs hC (by positivity) (by positivity)
    hVS hVT hwS hwT).trans
  apply ENNReal.ofReal_le_ofReal
  have he : (A*b/r^2)*(A*d/s^2)*(sphereArea+C)*s*C*r^3=
      (A^2*C*(sphereArea+C)*b*d)*(r/s) := by
    field_simp
  rw [he]
  exact mul_le_of_le_one_right (by positivity) ((div_le_one hs).mpr hrs)

theorem pairEnergy_scaled_unordered {w:E→ℝ≥0∞} (hw:Measurable w) {S T:Set E}
    (hS:MeasurableSet S) (hT:MeasurableSet T) {r s C A b d:ℝ}
    (hr:0<r) (hs:0<s) (hC:0≤C) (hA:0≤A) (hb:0≤b) (hd:0≤d)
    (hVS:volume S≤ENNReal.ofReal (C*r^3))
    (hVT:volume T≤ENNReal.ofReal (C*s^3))
    (hwS:∀k∈S,w k≤ENNReal.ofReal (A*b/r^2))
    (hwT:∀k∈T,w k≤ENNReal.ofReal (A*d/s^2)) :
    pairEnergy w S T ≤ ENNReal.ofReal (A^2*C*(sphereArea+C)*b*d) := by
  rcases le_total r s with hrs|hsr
  · exact pairEnergy_scaled hS hT hr hs hrs hC hA hb hd hVS hVT hwS hwT
  · rw [pairEnergy_symm hw]
    have h := pairEnergy_scaled hT hS hs hr hsr hC hA hd hb hVT hVS hwT hwS
    exact h.trans_eq (by congr 1; ring)

theorem pairEnergy_union_le {w:E→ℝ≥0∞} (hw:Measurable w) (S:ℕ→Set E) :
    pairEnergy w (⋃n,S n) (⋃n,S n) ≤ ∑'i:ℕ,∑'j:ℕ,pairEnergy w (S i) (S j) := by
  unfold pairEnergy
  apply (lintegral_iUnion_le _ _).trans
  apply ENNReal.tsum_le_tsum
  intro i
  calc
    _ ≤ ∫⁻k in S i,∑'j:ℕ,∫⁻p in S j,w k*w p*kernelTwo (k-p) := by
      apply lintegral_mono
      intro k
      exact lintegral_iUnion_le _ _
    _ = _ := by
      apply lintegral_tsum
      intro j
      apply Measurable.aemeasurable
      apply Measurable.lintegral_prod_right
      exact ((hw.comp measurable_fst).mul (hw.comp measurable_snd)).mul
        (kernelTwo_measurable.comp (measurable_fst.sub measurable_snd))

theorem union_energy_finite {w:E→ℝ≥0∞} (hw:Measurable w)
    (S:ℕ→Set E) (hS:∀n,MeasurableSet (S n)) (r b:ℕ→ℝ)
    (hr:∀n,0<r n) (hb:∀n,0≤b n) (hbs:Summable b) {C A:ℝ} (hC:0≤C) (hA:0≤A)
    (hV:∀n,volume (S n)≤ENNReal.ofReal (C*(r n)^3))
    (hwS:∀n k,k∈S n→w k≤ENNReal.ofReal (A*b n/(r n)^2)) :
    pairEnergy w (⋃n,S n) (⋃n,S n)<∞ := by
  let K : ℝ := A^2*C*(sphereArea+C)
  have hK : 0≤K := by dsimp [K]; have ha:=sphereArea_nonnegative; positivity
  have hpair (i j:ℕ) : pairEnergy w (S i) (S j)≤
      ENNReal.ofReal K*ENNReal.ofReal (b i)*ENNReal.ofReal (b j) := by
    have h := pairEnergy_scaled_unordered hw (hS i) (hS j) (hr i) (hr j)
      hC hA (hb i) (hb j) (hV i) (hV j) (hwS i) (hwS j)
    convert h using 1
    rw [←ENNReal.ofReal_mul hK,←ENNReal.ofReal_mul (mul_nonneg hK (hb i))]
  apply (pairEnergy_union_le hw S).trans_lt
  apply (ENNReal.tsum_le_tsum (fun i=>ENNReal.tsum_le_tsum (hpair i))).trans_lt
  simp_rw [ENNReal.tsum_mul_left,ENNReal.tsum_mul_right]
  rw [ENNReal.tsum_mul_left]
  exact ENNReal.mul_lt_top
    (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hbs.tsum_ofReal_lt_top) hbs.tsum_ofReal_lt_top

end
end Resonance.NewtonLayerEnergy
