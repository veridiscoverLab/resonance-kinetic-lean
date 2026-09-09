import Resonance.PairParameterBounds

/-! Uniform parameter differences of the actual loss frequency, with
the original complete fixed-output fiber retained at every cube point. -/
open MeasureTheory Set
open scoped BigOperators ENNReal
namespace Resonance.FrequencyParameterBounds
noncomputable section
set_option maxHeartbeats 1200000
open ResonantMeasure WeightedJointMeasure Thermodynamics CollisionFrequency CollisionFiber
open CollisionMarginalDensity ProfileParameterBounds QuartetParameterBounds

def triple (θ : Parameter) (q : FourMomenta) : ℝ :=
  profile θ (q 1)*profile θ (q 2)*profile θ (q 3)

theorem triple_eq_product (θ : Parameter) (q : FourMomenta) :
    triple θ q=∏i : Fin 3,profile θ (q i.succ) := by
  simp only [Fin.prod_univ_succ,Fin.prod_univ_zero,mul_one,triple]
  change profile θ (q 1)*profile θ (q 2)*profile θ (q 3)=
    profile θ (q 1)*(profile θ (q 2)*profile θ (q 3))
  ring

theorem triple_bounds {R L δ : ℝ} {θ β : Parameter}
    (hθ : θ∈positiveDomain R) (hβ : β∈positiveDomain R) (hL : 1≤L) (hδ : 0≤δ)
    (hθL : ∀k∈cube R,profile θ k≤L) (hβL : ∀k∈cube R,profile β k≤L)
    (hd : ∀k∈cube R,|profile θ k-profile β k|≤δ)
    {q : FourMomenta} (hq : q∈CoareaNormalization.allFourFlags R) :
    |triple θ q|≤L^3 ∧ |triple θ q-triple β q|≤3*L^3*δ := by
  constructor
  · rw [triple_eq_product,Finset.abs_prod]
    calc
      _ ≤ ∏_i : Fin 3,L := Finset.prod_le_prod (fun _ _=>abs_nonneg _)
        (fun i _=>by rw [abs_of_pos (profile_pos hθ (hq i.succ))]; exact hθL _ (hq i.succ))
      _ = _ := by simp
  · rw [triple_eq_product,triple_eq_product]
    exact finite_product_difference hL hδ _ _
      (fun i=>by rw [abs_of_pos (profile_pos hθ (hq i.succ))]; exact hθL _ (hq i.succ))
      (fun i=>by rw [abs_of_pos (profile_pos hβ (hq i.succ))]; exact hβL _ (hq i.succ))
      (fun i=>hd _ (hq i.succ))

theorem triple_integral_bounds {R L δ : ℝ} (hR : 0≤R) {θ β : Parameter}
    (hθ : θ∈positiveDomain R) (hβ : β∈positiveDomain R) (hL : 1≤L) (hδ : 0≤δ)
    (hθL : ∀k∈cube R,profile θ k≤L) (hβL : ∀k∈cube R,profile β k≤L)
    (hd : ∀k∈cube R,|profile θ k-profile β k|≤δ) (k : E) :
    |∫q,triple θ q∂fiberMeasure R k|≤L^3*geometricFrequency R k ∧
    |(∫q,triple θ q∂fiberMeasure R k)-(∫q,triple β q∂fiberMeasure R k)|≤
      (3*L^3*δ)*geometricFrequency R k := by
  letI : IsFiniteMeasure (fiberMeasure R k) := ⟨geometricFrequency_mass_finite hR k⟩
  have hiθ := triple_integrable hR (zero_le_one.trans hL) (profile_measurable θ)
    (fun p hp=>by rw [Real.norm_eq_abs,abs_of_pos (profile_pos hθ hp)]; exact hθL p hp) k
  have hiβ := triple_integrable hR (zero_le_one.trans hL) (profile_measurable β)
    (fun p hp=>by rw [Real.norm_eq_abs,abs_of_pos (profile_pos hβ hp)]; exact hβL p hp) k
  change Integrable (triple θ) (fiberMeasure R k) at hiθ
  change Integrable (triple β) (fiberMeasure R k) at hiβ
  have hc (a : ℝ) : (∫q,a∂fiberMeasure R k)=a*geometricFrequency R k := by
    simp only [integral_const,smul_eq_mul,measureReal_def,geometricFrequency_eq_mass,mul_comm]
  constructor
  · rw [←hc (L^3),←Real.norm_eq_abs]
    apply norm_integral_le_of_norm_le (integrable_const _)
    filter_upwards [fiber_support R k] with q hq
    simpa only [Real.norm_eq_abs] using (triple_bounds hθ hβ hL hδ hθL hβL hd hq.1).1
  · rw [←integral_sub hiθ hiβ,←hc (3*L^3*δ),←Real.norm_eq_abs]
    apply norm_integral_le_of_norm_le (integrable_const _)
    filter_upwards [fiber_support R k] with q hq
    simpa only [Real.norm_eq_abs] using (triple_bounds hθ hβ hL hδ hθL hβL hd hq.1).2

theorem loss_difference_bound {R m L C : ℝ} (hR : 0≤R) (hm : 0 < m)
    {θ β : Parameter} (hθ : θ∈positiveDomain R) (hβ : β∈positiveDomain R)
    (hL : 1≤L) (hC : 0≤C)
    (hθb : ∀k∈cube R,m≤profile θ k ∧ profile θ k≤L)
    (hβb : ∀k∈cube R,m≤profile β k ∧ profile β k≤L)
    (hd : ∀k∈cube R,|profile θ k-profile β k|≤C*‖θ-β‖)
    {k : E} (hk : k∈cube R) :
    |lossFrequency R (profile θ) k-lossFrequency R (profile β) k|≤
      (‖denominatorMap R‖*L^3+m⁻¹*(3*L^3*C))*‖θ-β‖*geometricFrequency R k := by
  obtain ⟨hI,hD⟩ := triple_integral_bounds hR hθ hβ hL (mul_nonneg hC (norm_nonneg _))
    (fun p hp=>(hθb p hp).2) (fun p hp=>(hβb p hp).2) hd k
  have hq : |(profile θ k)⁻¹-(profile β k)⁻¹|≤‖denominatorMap R‖*‖θ-β‖ := by
    simpa only [profile,Entropy.rj,inv_inv] using denominator_difference_bound R θ β hk
  have hb : |(profile β k)⁻¹| ≤ m⁻¹ := by
    rw [abs_of_pos (inv_pos.mpr (profile_pos hβ hk))]
    exact inv_anti₀ hm (hβb k hk).1
  have hL0 : 0≤L := zero_le_one.trans hL
  have hg : 0≤geometricFrequency R k := geometricFrequency_nonnegative R k
  change |(profile θ k)⁻¹*(∫q,triple θ q∂fiberMeasure R k)-
    (profile β k)⁻¹*(∫q,triple β q∂fiberMeasure R k)|≤_
  calc
    _ = |((profile θ k)⁻¹-(profile β k)⁻¹)*(∫q,triple θ q∂fiberMeasure R k)+
        (profile β k)⁻¹*((∫q,triple θ q∂fiberMeasure R k)-(∫q,triple β q∂fiberMeasure R k))| := by
      congr 1
      ring
    _ ≤ |((profile θ k)⁻¹-(profile β k)⁻¹)*(∫q,triple θ q∂fiberMeasure R k)|+
        |(profile β k)⁻¹*((∫q,triple θ q∂fiberMeasure R k)-(∫q,triple β q∂fiberMeasure R k))| :=
      abs_add_le _ _
    _ ≤ (‖denominatorMap R‖*‖θ-β‖)*(L^3*geometricFrequency R k)+
        m⁻¹*((3*L^3*(C*‖θ-β‖))*geometricFrequency R k) := by
      rw [abs_mul,abs_mul]
      exact add_le_add (mul_le_mul hq hI (abs_nonneg _) (by positivity))
        (mul_le_mul hb hD (abs_nonneg _) (inv_nonneg.mpr hm.le))
    _ = _ := by ring

theorem compact_loss_difference_bound {R : ℝ} (hR : 0≤R) {K : Set Parameter}
    (hK : IsCompact K) (hpos : K⊆positiveDomain R) :
    ∃a b C : ℝ,0<a ∧ 0<b ∧ 0≤C ∧
      (∀θ∈K,∀k∈cube R,a*geometricFrequency R k≤lossFrequency R (profile θ) k ∧
        lossFrequency R (profile θ) k≤b*geometricFrequency R k) ∧
      ∀θ∈K,∀β∈K,∀k∈cube R,
        |lossFrequency R (profile θ) k-lossFrequency R (profile β) k|≤C*‖θ-β‖*geometricFrequency R k := by
  obtain ⟨m,M,C,hm,hM,hC,hb,hd⟩ := compact_profile_lipschitz hR hK hpos
  let L := max M 1
  have hL : 0<L := lt_of_lt_of_le zero_lt_one (le_max_right M 1)
  have hb' : ∀θ∈K,∀k∈cube R,m≤profile θ k ∧ profile θ k≤L := by
    intro θ hθ k hk
    exact ⟨(hb θ hθ k hk).1,(hb θ hθ k hk).2.trans (le_max_left M 1)⟩
  refine ⟨m^3/L,L^3/m,‖denominatorMap R‖*L^3+m⁻¹*(3*L^3*C),
    div_pos (pow_pos hm 3) hL,div_pos (pow_pos hL 3) hm,by positivity,?_,?_⟩
  · intro θ hθ k hk
    exact lossFrequency_geometric_bounds hR hm hL (profile θ) (profile_measurable θ) (hb' θ hθ) hk
  · intro θ hθ β hβ k hk
    exact loss_difference_bound hR hm (hpos hθ) (hpos hβ) (le_max_right M 1) hC
      (hb' θ hθ) (hb' β hβ) (hd θ hθ β hβ) hk

end
end Resonance.FrequencyParameterBounds
