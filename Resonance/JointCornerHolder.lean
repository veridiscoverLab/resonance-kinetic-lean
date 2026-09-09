import Resonance.CornerPairTruncation

/-! Hölder interpolation inside the original common quartet measure.
No product replacement of that measure, no independent leg law, and no
spatial Sobolev hypothesis is used in these momentum inequalities. -/
open Set MeasureTheory Filter
open scoped ENNReal Topology
namespace Resonance.JointCornerHolder
noncomputable section
open ResonantMeasure WeightedJointMeasure FrequencyWeightedForm
open CornerPairTruncation
set_option maxHeartbeats 1500000

/-- The exact 2/3,1/3 integral inequality, including zero integrals. -/
theorem holder_two_one_data {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f g : α→ℝ} (hf : Integrable f μ) (hg : Integrable g μ)
    (hfn : ∀x,0≤f x) (hgn : ∀x,0≤g x) :
    Integrable (fun x=>(f x)^((2:ℝ)/3)*(g x)^((1:ℝ)/3)) μ ∧
    (∫x,(f x)^((2:ℝ)/3)*(g x)^((1:ℝ)/3)∂μ)
      ≤(∫x,f x∂μ)^((2:ℝ)/3)*(∫x,g x∂μ)^((1:ℝ)/3) := by
  have hfm : MemLp (fun x=>(f x)^((2:ℝ)/3)) (ENNReal.ofReal ((3:ℝ)/2)) μ := by
    have h:=(memLp_one_iff_integrable.mpr hf).norm_rpow_div ((2:ℝ≥0∞)/3)
    have he : (1:ℝ≥0∞)/((2:ℝ≥0∞)/3)=ENNReal.ofReal ((3:ℝ)/2) := by
      rw [one_div,ENNReal.inv_div (by norm_num) (by norm_num),
        ENNReal.ofReal_div_of_pos (by norm_num : (0:ℝ)<2)]
      norm_num
    rw [he] at h
    simpa only [ENNReal.toReal_div,ENNReal.toReal_ofNat,
      Real.norm_eq_abs,abs_of_nonneg (hfn _)] using h
  have hgm : MemLp (fun x=>(g x)^((1:ℝ)/3)) (ENNReal.ofReal (3:ℝ)) μ := by
    have h:=(memLp_one_iff_integrable.mpr hg).norm_rpow_div ((1:ℝ≥0∞)/3)
    have he : (1:ℝ≥0∞)/((1:ℝ≥0∞)/3)=ENNReal.ofReal (3:ℝ) := by norm_num
    rw [he] at h
    simpa only [ENNReal.toReal_div,ENNReal.toReal_ofNat,ENNReal.toReal_one,
      Real.norm_eq_abs,abs_of_nonneg (hgn _)] using h
  have hpq : ((3:ℝ)/2).HolderConjugate 3 := by norm_num [Real.holderConjugate_iff]
  have hb:=integral_mul_le_Lp_mul_Lq_of_nonneg hpq
    (ae_of_all _ (fun x=>Real.rpow_nonneg (hfn x) _))
    (ae_of_all _ (fun x=>Real.rpow_nonneg (hgn x) _)) hfm hgm
  have hfp : (fun x=>((f x)^((2:ℝ)/3))^((3:ℝ)/2))=f := by
    funext x
    rw [←Real.rpow_mul (hfn x)]
    norm_num
  have hgp : (fun x=>((g x)^((1:ℝ)/3))^(3:ℝ))=g := by
    funext x
    rw [←Real.rpow_mul (hgn x)]
    norm_num
  letI:=hpq.ennrealOfReal
  exact ⟨hfm.integrable_mul hgm,by
    simpa only [hfp,hgp,one_div_div,div_one] using hb⟩

theorem holder_two_one {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f g : α→ℝ} (hf : Integrable f μ) (hg : Integrable g μ)
    (hfn : ∀x,0≤f x) (hgn : ∀x,0≤g x) :
    (∫x,(f x)^((2:ℝ)/3)*(g x)^((1:ℝ)/3)∂μ)
      ≤(∫x,f x∂μ)^((2:ℝ)/3)*(∫x,g x∂μ)^((1:ℝ)/3) :=
  (holder_two_one_data hf hg hfn hgn).2

/-- A continuous or merely measurable L² reader is inserted at its actual
leg of the same weighted joint measure. -/
theorem actual_nonnegative_pair_bound {R : ℝ} {θ : Thermodynamics.Parameter}
    (i j : Fin 4) (hij : i≠j) (η : ℝ) {f g : E→ℝ}
    (hf : MemLp f 2 (marginal R θ)) (hg : MemLp g 2 (marginal R θ))
    (hfn : ∀k,0≤f k) (hgn : ∀k,0≤g k) :
    (∫q,(f (q i)*cut R η (q i))*(g (q j)*cut R η (q j))∂jointMeasure R θ)
      ≤omega R θ η*Real.sqrt (∫k,(f k)^2∂marginal R θ)*
        Real.sqrt (∫k,(g k)^2∂marginal R θ) := by
  have he : (∫q,(hf.toLp f (q i)*cut R η (q i))*(hg.toLp g (q j)*cut R η (q j))
      ∂jointMeasure R θ)=
      ∫q,(f (q i)*cut R η (q i))*(g (q j)*cut R η (q j))∂jointMeasure R θ := by
    apply integral_congr_ae
    filter_upwards [(all_legs_preserve R θ i).quasiMeasurePreserving.ae_eq hf.coeFn_toLp,
      (all_legs_preserve R θ j).quasiMeasurePreserving.ae_eq hg.coeFn_toLp] with q hi hj
    simp only [Function.comp_def] at hi hj
    rw [hi,hj]
  have hb:=actual_distinct_corner_pair_bound R θ i j hij η (hf.toLp f) (hg.toLp g)
  rw [he,abs_of_nonneg (integral_nonneg (fun q=>
    mul_nonneg (mul_nonneg (hfn _) (cut_bounds R η _).1)
      (mul_nonneg (hgn _) (cut_bounds R η _).1))),
    FixedMultiplier.L2_norm_eq_sqrt,FixedMultiplier.L2_norm_eq_sqrt] at hb
  simpa only [Real.norm_eq_abs,sq_abs] using hb

theorem actual_cut_pair_integrable {R : ℝ} {θ : Thermodynamics.Parameter}
    (i j : Fin 4) (η : ℝ) {f g : E→ℝ}
    (hf : MemLp f 2 (marginal R θ)) (hg : MemLp g 2 (marginal R θ)) :
    Integrable (fun q:FourMomenta=>(f (q i)*cut R η (q i))*(g (q j)*cut R η (q j)))
      (jointMeasure R θ) := by
  apply (cut_joint_product_integrable R θ i j η (hf.toLp f) (hg.toLp g)).congr
  filter_upwards [(all_legs_preserve R θ i).quasiMeasurePreserving.ae_eq hf.coeFn_toLp,
    (all_legs_preserve R θ j).quasiMeasurePreserving.ae_eq hg.coeFn_toLp] with q hi hj
  simp only [Function.comp_def] at hi hj
  rw [hi,hj]

theorem actual_leg_integral (R : ℝ) (θ : Thermodynamics.Parameter) (i : Fin 4)
    {f : E→ℝ} (hf : Integrable f (marginal R θ)) :
    (∫q,f (q i)∂jointMeasure R θ)=∫k,f k∂marginal R θ := by
  have ha : AEStronglyMeasurable f ((jointMeasure R θ).map (fun q=>q i)) := by
    rw [(all_legs_preserve R θ i).map_eq]
    exact hf.aestronglyMeasurable
  rw [←integral_map (measurable_pi_apply i).aemeasurable ha,
    (all_legs_preserve R θ i).map_eq]

theorem actual_cut_leg_square_integrable {R : ℝ} {θ : Thermodynamics.Parameter}
    (i : Fin 4) (η : ℝ) {f : E→ℝ} (hf : MemLp f 2 (marginal R θ)) :
    Integrable (fun q:FourMomenta=>(f (q i)*cut R η (q i))^2) (jointMeasure R θ) := by
  have hm : MemLp (fun k=>f k*cut R η k) 2 (marginal R θ) :=
    (cut_memLp R η (marginal R θ)).mul' hf
  exact (all_legs_preserve R θ i).integrable_comp_of_integrable hm.integrable_sq

theorem actual_cut_leg_square_le {R : ℝ} {θ : Thermodynamics.Parameter}
    (i : Fin 4) (η : ℝ) {f : E→ℝ} (hf : MemLp f 2 (marginal R θ)) :
    (∫q,(f (q i)*cut R η (q i))^2∂jointMeasure R θ)≤∫k,(f k)^2∂marginal R θ := by
  rw [←actual_leg_integral R θ i hf.integrable_sq]
  apply integral_mono (actual_cut_leg_square_integrable i η hf)
    ((all_legs_preserve R θ i).integrable_comp_of_integrable hf.integrable_sq)
  intro q
  have hb : |f (q i)*cut R η (q i)|≤|f (q i)| := by
    rw [abs_mul]
    exact (mul_le_mul_of_nonneg_left (cut_bounds R η _).2 (abs_nonneg _)).trans_eq (mul_one _)
  simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) hb 2

theorem scalar_two_one_factor {a b : ℝ} (ha : 0≤a) (hb : 0≤b) :
    (a*b)^((2:ℝ)/3)*(a^2)^((1:ℝ)/3)=a^((4:ℝ)/3)*b^((2:ℝ)/3) := by
  rw [Real.mul_rpow ha hb,←Real.rpow_natCast,←Real.rpow_mul ha]
  have hp : a^((2:ℝ)/3)*a^((2:ℝ)/3)=a^((4:ℝ)/3) := by
    rw [←Real.rpow_add_of_nonneg ha (by norm_num) (by norm_num)]
    norm_num
  calc
    a^((2:ℝ)/3)*b^((2:ℝ)/3)*a^((2:ℝ)*(1/3))
        =(a^((2:ℝ)/3)*a^((2:ℝ)/3))*b^((2:ℝ)/3) := by norm_num; ring
    _ =_ := by rw [hp]

theorem scalar_two_one_bound_factor {w a b : ℝ} (hw : 0≤w) (ha : 0≤a) (hb : 0≤b) :
    (w*Real.sqrt a*Real.sqrt b)^((2:ℝ)/3)*a^((1:ℝ)/3)
      =w^((2:ℝ)/3)*a^((2:ℝ)/3)*b^((1:ℝ)/3) := by
  rw [Real.mul_rpow (mul_nonneg hw (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _),
    Real.mul_rpow hw (Real.sqrt_nonneg _),Real.sqrt_eq_rpow,Real.sqrt_eq_rpow,
    ←Real.rpow_mul ha,←Real.rpow_mul hb]
  have hp : a^((1:ℝ)/3)*a^((1:ℝ)/3)=a^((2:ℝ)/3) := by
    rw [←Real.rpow_add_of_nonneg ha (by norm_num) (by norm_num)]
    norm_num
  calc
    w^((2:ℝ)/3)*a^((1:ℝ)/2*(2/3))*b^((1:ℝ)/2*(2/3))*a^((1:ℝ)/3)
        =w^((2:ℝ)/3)*(a^((1:ℝ)/3)*a^((1:ℝ)/3))*b^((1:ℝ)/3) := by norm_num; ring
    _ =_ := by rw [hp]

/-- The 2+1 derivative allocation's actual two-leg momentum inequality.
This is proved by Hölder on the complete joint measure, not interpolation
of independently sampled legs. -/
theorem actual_two_one_corner_bound {R : ℝ} {θ : Thermodynamics.Parameter}
    (i j : Fin 4) (hij : i≠j) (η : ℝ) {f g : E→ℝ}
    (hf : MemLp f 2 (marginal R θ)) (hg : MemLp g 2 (marginal R θ))
    (hfn : ∀k,0≤f k) (hgn : ∀k,0≤g k) :
    (∫q,(f (q i)*cut R η (q i))^((4:ℝ)/3)*
      (g (q j)*cut R η (q j))^((2:ℝ)/3)∂jointMeasure R θ)
      ≤(omega R θ η)^((2:ℝ)/3)*(∫k,(f k)^2∂marginal R θ)^((2:ℝ)/3)*
        (∫k,(g k)^2∂marginal R θ)^((1:ℝ)/3) := by
  let A : FourMomenta→ℝ:=fun q=>(f (q i)*cut R η (q i))*(g (q j)*cut R η (q j))
  let B : FourMomenta→ℝ:=fun q=>(f (q i)*cut R η (q i))^2
  have hAn : ∀q,0≤A q:=fun q=>mul_nonneg
    (mul_nonneg (hfn _) (cut_bounds R η _).1) (mul_nonneg (hgn _) (cut_bounds R η _).1)
  have hBn : ∀q,0≤B q:=fun _=>sq_nonneg _
  have hb:=holder_two_one (actual_cut_pair_integrable i j η hf hg)
    (actual_cut_leg_square_integrable i η hf) hAn hBn
  have he : (fun q:FourMomenta=>(A q)^((2:ℝ)/3)*(B q)^((1:ℝ)/3))=
      (fun q=>(f (q i)*cut R η (q i))^((4:ℝ)/3)*
        (g (q j)*cut R η (q j))^((2:ℝ)/3)) := by
    funext q
    exact scalar_two_one_factor (mul_nonneg (hfn _) (cut_bounds R η _).1)
      (mul_nonneg (hgn _) (cut_bounds R η _).1)
  change (∫q,(A q)^((2:ℝ)/3)*(B q)^((1:ℝ)/3)∂jointMeasure R θ)≤_ at hb
  rw [he] at hb
  apply hb.trans
  calc
    (∫q,A q∂jointMeasure R θ)^((2:ℝ)/3)*(∫q,B q∂jointMeasure R θ)^((1:ℝ)/3)
      ≤(omega R θ η*Real.sqrt (∫k,(f k)^2∂marginal R θ)*
          Real.sqrt (∫k,(g k)^2∂marginal R θ))^((2:ℝ)/3)*
        (∫k,(f k)^2∂marginal R θ)^((1:ℝ)/3) := by
        exact mul_le_mul
          (Real.rpow_le_rpow (integral_nonneg hAn)
            (actual_nonnegative_pair_bound i j hij η hf hg hfn hgn) (by norm_num))
          (Real.rpow_le_rpow (integral_nonneg hBn)
            (actual_cut_leg_square_le i η hf) (by norm_num))
          (Real.rpow_nonneg (integral_nonneg hBn) _)
          (Real.rpow_nonneg (mul_nonneg (mul_nonneg (omega_nonnegative R θ η)
            (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _)) _)
    _ =_ := scalar_two_one_bound_factor (omega_nonnegative R θ η)
      (integral_nonneg (fun _=>sq_nonneg _)) (integral_nonneg (fun _=>sq_nonneg _))

theorem actual_two_one_corner_integrable {R : ℝ} {θ : Thermodynamics.Parameter}
    (i j : Fin 4) (η : ℝ) {f g : E→ℝ}
    (hf : MemLp f 2 (marginal R θ)) (hg : MemLp g 2 (marginal R θ))
    (hfn : ∀k,0≤f k) (hgn : ∀k,0≤g k) :
    Integrable (fun q:FourMomenta=>(f (q i)*cut R η (q i))^((4:ℝ)/3)*
      (g (q j)*cut R η (q j))^((2:ℝ)/3)) (jointMeasure R θ) := by
  have h:=(holder_two_one_data (actual_cut_pair_integrable i j η hf hg)
    (actual_cut_leg_square_integrable i η hf)
    (fun q=>mul_nonneg (mul_nonneg (hfn _) (cut_bounds R η _).1)
      (mul_nonneg (hgn _) (cut_bounds R η _).1)) (fun _=>sq_nonneg _)).1
  exact h.congr (ae_of_all _ (fun _=>scalar_two_one_factor
    (mul_nonneg (hfn _) (cut_bounds R η _).1)
    (mul_nonneg (hgn _) (cut_bounds R η _).1)))

theorem scalar_three_factor {a b d : ℝ} (ha : 0≤a) (hb : 0≤b) (hd : 0≤d) :
    (a*b)^((2:ℝ)/3)*(d^2)^((1:ℝ)/3)=
      a^((2:ℝ)/3)*b^((2:ℝ)/3)*d^((2:ℝ)/3) := by
  rw [Real.mul_rpow ha hb,←Real.rpow_natCast,←Real.rpow_mul hd]
  norm_num

theorem scalar_three_bound_factor {w a b d : ℝ} (hw : 0≤w) (ha : 0≤a) (hb : 0≤b) :
    (w*Real.sqrt a*Real.sqrt b)^((2:ℝ)/3)*d^((1:ℝ)/3)=
      w^((2:ℝ)/3)*a^((1:ℝ)/3)*b^((1:ℝ)/3)*d^((1:ℝ)/3) := by
  rw [Real.mul_rpow (mul_nonneg hw (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _),
    Real.mul_rpow hw (Real.sqrt_nonneg _),Real.sqrt_eq_rpow,Real.sqrt_eq_rpow,
    ←Real.rpow_mul ha,←Real.rpow_mul hb]
  norm_num

/-- The three positive-derivative legs stay on the same quartet. Only one
distinct pair is needed for the actual small factor. -/
theorem actual_three_leg_corner_data {R : ℝ} {θ : Thermodynamics.Parameter}
    (i j k : Fin 4) (hij : i≠j) (η : ℝ) {f g h : E→ℝ}
    (hf : MemLp f 2 (marginal R θ)) (hg : MemLp g 2 (marginal R θ))
    (hh : MemLp h 2 (marginal R θ))
    (hfn : ∀p,0≤f p) (hgn : ∀p,0≤g p) (hhn : ∀p,0≤h p) :
    Integrable (fun q:FourMomenta=>(f (q i)*cut R η (q i))^((2:ℝ)/3)*
      (g (q j)*cut R η (q j))^((2:ℝ)/3)*(h (q k)*cut R η (q k))^((2:ℝ)/3))
      (jointMeasure R θ) ∧
    (∫q,(f (q i)*cut R η (q i))^((2:ℝ)/3)*
      (g (q j)*cut R η (q j))^((2:ℝ)/3)*(h (q k)*cut R η (q k))^((2:ℝ)/3)
        ∂jointMeasure R θ)
      ≤(omega R θ η)^((2:ℝ)/3)*(∫p,(f p)^2∂marginal R θ)^((1:ℝ)/3)*
        (∫p,(g p)^2∂marginal R θ)^((1:ℝ)/3)*(∫p,(h p)^2∂marginal R θ)^((1:ℝ)/3) := by
  let A : FourMomenta→ℝ:=fun q=>(f (q i)*cut R η (q i))*(g (q j)*cut R η (q j))
  let B : FourMomenta→ℝ:=fun q=>(h (q k)*cut R η (q k))^2
  have hAn : ∀q,0≤A q:=fun q=>mul_nonneg
    (mul_nonneg (hfn _) (cut_bounds R η _).1) (mul_nonneg (hgn _) (cut_bounds R η _).1)
  have hBn : ∀q,0≤B q:=fun _=>sq_nonneg _
  have hd:=holder_two_one_data (actual_cut_pair_integrable i j η hf hg)
    (actual_cut_leg_square_integrable k η hh) hAn hBn
  have he : (fun q:FourMomenta=>(A q)^((2:ℝ)/3)*(B q)^((1:ℝ)/3))=
      (fun q=>(f (q i)*cut R η (q i))^((2:ℝ)/3)*
        (g (q j)*cut R η (q j))^((2:ℝ)/3)*(h (q k)*cut R η (q k))^((2:ℝ)/3)) := by
    funext q
    exact scalar_three_factor (mul_nonneg (hfn _) (cut_bounds R η _).1)
      (mul_nonneg (hgn _) (cut_bounds R η _).1)
      (mul_nonneg (hhn _) (cut_bounds R η _).1)
  change Integrable (fun q=>(A q)^((2:ℝ)/3)*(B q)^((1:ℝ)/3)) _ ∧ _ at hd
  refine ⟨by simpa only [he] using hd.1,?_⟩
  have hb:=hd.2
  change (∫q,(A q)^((2:ℝ)/3)*(B q)^((1:ℝ)/3)∂jointMeasure R θ)≤_ at hb
  rw [he] at hb
  apply hb.trans
  calc
    (∫q,A q∂jointMeasure R θ)^((2:ℝ)/3)*(∫q,B q∂jointMeasure R θ)^((1:ℝ)/3)
      ≤(omega R θ η*Real.sqrt (∫p,(f p)^2∂marginal R θ)*
          Real.sqrt (∫p,(g p)^2∂marginal R θ))^((2:ℝ)/3)*
        (∫p,(h p)^2∂marginal R θ)^((1:ℝ)/3) := by
        exact mul_le_mul
          (Real.rpow_le_rpow (integral_nonneg hAn)
            (actual_nonnegative_pair_bound i j hij η hf hg hfn hgn) (by norm_num))
          (Real.rpow_le_rpow (integral_nonneg hBn)
            (actual_cut_leg_square_le k η hh) (by norm_num))
          (Real.rpow_nonneg (integral_nonneg hBn) _)
          (Real.rpow_nonneg (mul_nonneg (mul_nonneg (omega_nonnegative R θ η)
            (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _)) _)
    _ =_ := scalar_three_bound_factor (omega_nonnegative R θ η)
      (integral_nonneg (fun _=>sq_nonneg _)) (integral_nonneg (fun _=>sq_nonneg _))

end
end Resonance.JointCornerHolder
