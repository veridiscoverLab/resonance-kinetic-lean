import Resonance.ProfileParameterBounds

/-! Bounds for differences of the same full four-leg RJ weight.
The product estimate is applied before the actual pair pushforwards. -/
open MeasureTheory Set
open scoped BigOperators ENNReal
namespace Resonance.QuartetParameterBounds
noncomputable section
set_option maxHeartbeats 1000000
open ResonantMeasure WeightedJointMeasure Thermodynamics JointWeightComparison

theorem finite_product_difference {n : ℕ} {L δ : ℝ} (hL : 1≤L) (hδ : 0≤δ)
    (a b : Fin n→ℝ) (ha : ∀i,|a i|≤L) (hb : ∀i,|b i|≤L)
    (hd : ∀i,|a i-b i|≤δ) :
    |(∏i,a i)-(∏i,b i)|≤(n : ℝ)*L^n*δ := by
  have hL0 : 0≤L := le_trans zero_le_one hL
  induction n with
  | zero => simp
  | succ n ih =>
    have hp : |∏i : Fin n,b i.succ|≤L^n := by
      rw [Finset.abs_prod]
      exact (Finset.prod_le_prod (fun _ _=>abs_nonneg _)
        (fun i _=>hb i.succ)).trans_eq (by simp)
    have hi := ih (fun i=>a i.succ) (fun i=>b i.succ)
      (fun i=>ha i.succ) (fun i=>hb i.succ) (fun i=>hd i.succ)
    rw [Fin.prod_univ_succ,Fin.prod_univ_succ]
    calc
      _ = |a 0*((∏i : Fin n,a i.succ)-(∏i : Fin n,b i.succ))+
          (a 0-b 0)*(∏i : Fin n,b i.succ)| := by congr 1; ring
      _ ≤ |a 0*((∏i : Fin n,a i.succ)-(∏i : Fin n,b i.succ))|+
          |(a 0-b 0)*(∏i : Fin n,b i.succ)| := abs_add_le _ _
      _ ≤ L*((n : ℝ)*L^n*δ)+δ*L^n := by
        rw [abs_mul,abs_mul]
        exact add_le_add (mul_le_mul (ha 0) hi (abs_nonneg _) hL0)
          (mul_le_mul (hd 0) hp (abs_nonneg _) hδ)
      _ ≤ ((n+1 : ℕ) : ℝ)*L^(n+1)*δ := by
        rw [Nat.cast_add,Nat.cast_one,pow_succ]
        nlinarith [mul_nonneg (pow_nonneg hL0 n) hδ,
          mul_nonneg (sub_nonneg.mpr hL) (mul_nonneg (pow_nonneg hL0 n) hδ)]

theorem quartet_weight_order {R L δ : ℝ} {θ β : Parameter}
    (hθ : θ∈positiveDomain R) (hβ : β∈positiveDomain R)
    (hL : 1≤L) (hδ : 0≤δ)
    (hθL : ∀k∈cube R,profile θ k≤L) (hβL : ∀k∈cube R,profile β k≤L)
    (hd : ∀k∈cube R,|profile θ k-profile β k|≤δ)
    {q : FourMomenta} (hq : q∈CoareaNormalization.allFourFlags R) :
    weight θ q≤weight β q+ENNReal.ofReal (4*L^4*δ) := by
  have hp := finite_product_difference hL hδ (fun i : Fin 4=>profile θ (q i))
    (fun i=>profile β (q i))
    (fun i=>by rw [abs_of_pos (profile_pos hθ (hq i))]; exact hθL _ (hq i))
    (fun i=>by rw [abs_of_pos (profile_pos hβ (hq i))]; exact hβL _ (hq i))
    (fun i=>hd _ (hq i))
  have hn : 0≤∏i : Fin 4,profile β (q i) := Finset.prod_nonneg
    (fun i _=>(profile_pos hβ (hq i)).le)
  have he : (∏i : Fin 4,profile θ (q i))≤(∏i : Fin 4,profile β (q i))+4*L^4*δ := by
    have hs := (abs_le.mp hp).2
    norm_num at hs
    linarith
  rw [weight,weight,←ENNReal.ofReal_add hn (by positivity)]
  exact ENNReal.ofReal_le_ofReal he

theorem compact_quartet_weight_order {R : ℝ} (hR : 0≤R) {K : Set Parameter}
    (hK : IsCompact K) (hpos : K⊆positiveDomain R) :
    ∃C : ℝ,0≤C ∧ ∀θ∈K,∀β∈K,∀q∈CoareaNormalization.allFourFlags R,
      weight θ q≤weight β q+ENNReal.ofReal (C*‖θ-β‖) := by
  obtain ⟨m,M,C,hm,hM,hC,hb,hd⟩ := ProfileParameterBounds.compact_profile_lipschitz hR hK hpos
  let L := max M 1
  refine ⟨4*L^4*C,by positivity,?_⟩
  intro θ hθ β hβ q hq
  have he := quartet_weight_order (hpos hθ) (hpos hβ) (le_max_right M 1)
    (mul_nonneg hC (norm_nonneg _))
    (fun k hk=>(hb θ hθ k hk).2.trans (le_max_left M 1))
    (fun k hk=>(hb β hβ k hk).2.trans (le_max_left M 1))
    (fun k hk=>hd θ hθ β hβ k hk) hq
  simpa only [mul_assoc] using he

end
end Resonance.QuartetParameterBounds
