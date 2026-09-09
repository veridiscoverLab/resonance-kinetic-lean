import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.MeasureTheory.Integral.Prod

/-! Height-free product-kernel bounds for the first critical chart F=-uV.
The small-u and large-u regions are estimated in the same original integral. -/
open Set MeasureTheory Filter
open scoped ENNReal Topology
namespace Resonance.ProductKernelSplit
noncomputable section

theorem scaled_mass {ρ:ℝ→ℝ≥0∞} (hm:Measurable ρ) (hρ:∫⁻s,ρ s=1)
    {u:ℝ} (hu:u≠0) : (∫⁻v,ρ (u*v))=ENNReal.ofReal (|u|⁻¹) := by
  have hc:=lintegral_image_eq_lintegral_abs_deriv_mul (s:=(univ:Set ℝ))
    (f:=fun v:ℝ=>u*v) (f':=fun _=>u) MeasurableSet.univ
    (fun v _=>by simpa using ((hasDerivAt_id v).const_mul u))
    (fun _ _ _ _ h=>mul_left_cancel₀ hu h) ρ
  have him:(fun v:ℝ=>u*v) '' (univ:Set ℝ)=univ:=by
    apply image_univ_of_surjective
    intro s
    exact ⟨s/u,by field_simp⟩
  have hcomp : Measurable (fun v : ℝ => ρ (u*v)) := hm.comp (measurable_const_mul u)
  rw [him] at hc
  simp only [Measure.restrict_univ] at hc
  rw [hρ,lintegral_const_mul _ hcomp] at hc
  have hi : (∫⁻v,ρ (u*v)) = (ENNReal.ofReal |u|)⁻¹ :=
    ENNReal.eq_inv_of_mul_eq_one_left (by simpa only [mul_comm] using hc.symm)
  rw [ENNReal.ofReal_inv_of_pos (abs_pos.mpr hu)]
  exact hi

def slice (ρ:ℝ→ℝ≥0∞) (L u:ℝ) : ℝ≥0∞ :=
  ∫⁻v in Icc (-L) L,ENNReal.ofReal |u*v| * ρ (u*v)

theorem slice_bound_length {ρ:ℝ→ℝ≥0∞} (hm:Measurable ρ) (hρ:∫⁻s,ρ s=1)
    {L:ℝ} (hL:0≤L) (u:ℝ) : slice ρ L u≤ENNReal.ofReal L := by
  by_cases hu:u=0
  · simp [slice,hu]
  · have hcomp : Measurable (fun v : ℝ => ρ (u*v)) := hm.comp (measurable_const_mul u)
    have ha:∀v∈Icc (-L) L,|u*v| ≤ |u| * L:=by
      intro v hv
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (abs_le.mpr hv) (abs_nonneg u)
    calc
      _ ≤ ∫⁻v in Icc (-L) L,ENNReal.ofReal (|u| * L)*ρ (u*v):=by
        apply lintegral_mono_ae
        filter_upwards [ae_restrict_mem measurableSet_Icc] with v hv
        exact mul_le_mul' (ENNReal.ofReal_le_ofReal (ha v hv)) le_rfl
      _ ≤ ∫⁻v,ENNReal.ofReal (|u| * L)*ρ (u*v):=lintegral_mono' Measure.restrict_le_self le_rfl
      _ = ENNReal.ofReal (|u| * L)*ENNReal.ofReal (|u|⁻¹):=by
        rw [lintegral_const_mul _ hcomp,scaled_mass hm hρ hu]
      _ = ENNReal.ofReal L:=by
        rw [←ENNReal.ofReal_mul (mul_nonneg (abs_nonneg u) hL)]
        congr 1
        field_simp [abs_ne_zero.mpr hu]

theorem slice_bound_support {ρ:ℝ→ℝ≥0∞} (hm:Measurable ρ) (hρ:∫⁻s,ρ s=1)
    {η:ℝ} (hη:0≤η) (hs:∀s,ρ s≠0→|s|≤η) (L:ℝ)
    {u:ℝ} (hu:u≠0) : slice ρ L u≤ENNReal.ofReal (η/|u|) := by
  have hcomp : Measurable (fun v : ℝ => ρ (u*v)) := hm.comp (measurable_const_mul u)
  calc
    _ ≤ ∫⁻v in Icc (-L) L,ENNReal.ofReal η*ρ (u*v):=by
      apply lintegral_mono
      intro v
      by_cases hv:ρ (u*v)=0
      · simp [hv]
      · exact mul_le_mul' (ENNReal.ofReal_le_ofReal (hs _ hv)) le_rfl
    _ ≤ ∫⁻v,ENNReal.ofReal η*ρ (u*v):=lintegral_mono' Measure.restrict_le_self le_rfl
    _ = ENNReal.ofReal η*ENNReal.ofReal (|u|⁻¹):=by
      rw [lintegral_const_mul _ hcomp,scaled_mass hm hρ hu]
    _ = _:=by rw [←ENNReal.ofReal_mul hη,div_eq_mul_inv]

theorem product_split_bound {ρ:ℝ→ℝ≥0∞} (hm:Measurable ρ) (hρ:∫⁻s,ρ s=1)
    {L η δ:ℝ} (hL:0≤L) (hη:0≤η) (hδ:0<δ)
    (hs:∀s,ρ s≠0→|s|≤η) :
    (∫⁻u in Icc (-L) L,slice ρ L u)≤ENNReal.ofReal (2*L*δ+2*L*(η/δ)) := by
  have hb:∀u,slice ρ L u≤
      (Icc (-δ) δ).indicator (fun _=>ENNReal.ofReal L) u+ENNReal.ofReal (η/δ):=by
    intro u
    by_cases hu:u∈Icc (-δ) δ
    · rw [Set.indicator_of_mem hu]
      exact (slice_bound_length hm hρ hL u).trans (le_add_right le_rfl)
    · rw [Set.indicator_of_notMem hu,zero_add]
      have huδ:δ < |u|:=lt_of_not_ge (fun h=>hu (abs_le.mp h))
      have hu0:u≠0:=abs_pos.mp (hδ.trans huδ)
      exact (slice_bound_support hm hρ hη hs L hu0).trans
        (ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_left hη hδ huδ.le))
  have hfirst:(∫⁻u in Icc (-L) L,(Icc (-δ) δ).indicator (fun _=>ENNReal.ofReal L) u)≤
      ENNReal.ofReal (2*L*δ):=by
    calc
      _ ≤ ∫⁻u,(Icc (-δ) δ).indicator (fun _=>ENNReal.ofReal L) u:=
        lintegral_mono' Measure.restrict_le_self le_rfl
      _ = ENNReal.ofReal L*ENNReal.ofReal (2*δ):=by
        rw [lintegral_indicator measurableSet_Icc,lintegral_const,Measure.restrict_apply_univ,
          Real.volume_Icc]
        congr 2
        ring
      _ = _:=by rw [←ENNReal.ofReal_mul hL]; congr 1; ring
  calc
    _ ≤ ∫⁻u in Icc (-L) L,
        (Icc (-δ) δ).indicator (fun _=>ENNReal.ofReal L) u+ENNReal.ofReal (η/δ):=
      lintegral_mono hb
    _ = (∫⁻u in Icc (-L) L,(Icc (-δ) δ).indicator (fun _=>ENNReal.ofReal L) u)+
        ENNReal.ofReal (2*L*(η/δ)):=by
      rw [lintegral_add_left (measurable_const.indicator measurableSet_Icc),lintegral_const,
        Measure.restrict_apply_univ,Real.volume_Icc]
      congr 1
      rw [←ENNReal.ofReal_mul (div_nonneg hη hδ.le)]
      congr 1
      ring
    _ ≤ ENNReal.ofReal (2*L*δ)+ENNReal.ofReal (2*L*(η/δ)):=add_le_add hfirst le_rfl
    _ = _:=by rw [ENNReal.ofReal_add (by positivity) (by positivity)]

theorem product_sqrt_bound {ρ:ℝ→ℝ≥0∞} (hm:Measurable ρ) (hρ:∫⁻s,ρ s=1)
    {L η:ℝ} (hL:0≤L) (hη:0<η) (hs:∀s,ρ s≠0→|s|≤η) :
    (∫⁻u in Icc (-L) L,slice ρ L u)≤ENNReal.ofReal (4*L*Real.sqrt η) := by
  have h:=product_split_bound hm hρ hL hη.le (Real.sqrt_pos.mpr hη) hs
  have he:η/Real.sqrt η=Real.sqrt η:=by
    apply (div_eq_iff (ne_of_gt (Real.sqrt_pos.mpr hη))).mpr
    nlinarith [Real.sq_sqrt hη.le]
  simpa only [he,show 2*L*Real.sqrt η+2*L*Real.sqrt η=4*L*Real.sqrt η by ring] using h

theorem product_squared_bound {ρ : ℝ → ℝ≥0∞} (hm : Measurable ρ)
    (hρ : ∫⁻s, ρ s = 1) {L η : ℝ} (hL : 0 ≤ L) (hη : 0 < η)
    (hs : ∀s, ρ s ≠ 0 → |s| ≤ η) :
    (∫⁻u in Icc (-L) L, ∫⁻v in Icc (-L) L,
      ENNReal.ofReal ((u*v)^2) * ρ (u*v)) ≤ ENNReal.ofReal (4*L*η*Real.sqrt η) := by
  have hp : ∀u v : ℝ, ENNReal.ofReal ((u*v)^2) * ρ (u*v) ≤
      ENNReal.ofReal η * (ENNReal.ofReal |u*v| * ρ (u*v)) := by
    intro u v
    by_cases hz : ρ (u*v) = 0
    · simp [hz]
    · rw [←mul_assoc, ←ENNReal.ofReal_mul hη.le]
      apply mul_le_mul' _ le_rfl
      apply ENNReal.ofReal_le_ofReal
      calc
        (u*v)^2 = |u*v| * |u*v| := by rw [←pow_two, sq_abs]
        _ ≤ η * |u*v| := mul_le_mul_of_nonneg_right (hs _ hz) (abs_nonneg _)
  calc
    _ ≤ ∫⁻u in Icc (-L) L, ∫⁻v in Icc (-L) L,
        ENNReal.ofReal η * (ENNReal.ofReal |u*v| * ρ (u*v)) :=
      lintegral_mono (fun u => lintegral_mono (hp u))
    _ = ENNReal.ofReal η * (∫⁻u in Icc (-L) L, slice ρ L u) := by
      simp_rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      rfl
    _ ≤ ENNReal.ofReal η * ENNReal.ofReal (4*L*Real.sqrt η) :=
      mul_le_mul' le_rfl (product_sqrt_bound hm hρ hL hη hs)
    _ = _ := by rw [←ENNReal.ofReal_mul hη.le]; congr 1; ring

theorem product_amplitude_bound {ρ : ℝ → ℝ≥0∞} (hm : Measurable ρ)
    (hρ : ∫⁻s, ρ s = 1) {L η C : ℝ} (hL : 0 ≤ L) (hη : 0 < η)
    (hC : 0 ≤ C) (hs : ∀s, ρ s ≠ 0 → |s| ≤ η)
    (A : ℝ × ℝ → ℝ≥0∞) (hA : ∀u v, A (u,v) ≤ ENNReal.ofReal (C*|u*v|)) :
    (∫⁻u in Icc (-L) L, ∫⁻v in Icc (-L) L, A (u,v) * ρ (u*v)) ≤
      ENNReal.ofReal (4*C*L*Real.sqrt η) := by
  calc
    _ ≤ ∫⁻u in Icc (-L) L, ∫⁻v in Icc (-L) L,
        ENNReal.ofReal (C*|u*v|) * ρ (u*v) :=
      lintegral_mono (fun u => lintegral_mono (fun v => mul_le_mul' (hA u v) le_rfl))
    _ = ENNReal.ofReal C * (∫⁻u in Icc (-L) L, slice ρ L u) := by
      simp_rw [ENNReal.ofReal_mul hC, mul_assoc,
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      rfl
    _ ≤ ENNReal.ofReal C * ENNReal.ofReal (4*L*Real.sqrt η) :=
      mul_le_mul' le_rfl (product_sqrt_bound hm hρ hL hη hs)
    _ = _ := by rw [←ENNReal.ofReal_mul hC]; congr 1; ring

theorem product_squared_amplitude_bound {ρ : ℝ → ℝ≥0∞} (hm : Measurable ρ)
    (hρ : ∫⁻s, ρ s = 1) {L η C : ℝ} (hL : 0 ≤ L) (hη : 0 < η)
    (hC : 0 ≤ C) (hs : ∀s, ρ s ≠ 0 → |s| ≤ η)
    (A : ℝ × ℝ → ℝ≥0∞) (hA : ∀u v, A (u,v) ≤ ENNReal.ofReal (C*(u*v)^2)) :
    (∫⁻u in Icc (-L) L, ∫⁻v in Icc (-L) L, A (u,v) * ρ (u*v)) ≤
      ENNReal.ofReal (4*C*L*η*Real.sqrt η) := by
  calc
    _ ≤ ∫⁻u in Icc (-L) L, ∫⁻v in Icc (-L) L,
        ENNReal.ofReal (C*(u*v)^2) * ρ (u*v) :=
      lintegral_mono (fun u => lintegral_mono (fun v => mul_le_mul' (hA u v) le_rfl))
    _ = ENNReal.ofReal C * (∫⁻u in Icc (-L) L, ∫⁻v in Icc (-L) L,
        ENNReal.ofReal ((u*v)^2) * ρ (u*v)) := by
      simp_rw [ENNReal.ofReal_mul hC, mul_assoc,
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    _ ≤ ENNReal.ofReal C * ENNReal.ofReal (4*L*η*Real.sqrt η) :=
      mul_le_mul' le_rfl (product_squared_bound hm hρ hL hη hs)
    _ = _ := by rw [←ENNReal.ofReal_mul hC]; congr 1; ring

end
end Resonance.ProductKernelSplit
