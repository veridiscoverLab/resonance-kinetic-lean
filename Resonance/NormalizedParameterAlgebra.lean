import Resonance.FrequencyParameterBounds

/-! Quantitative normalization of the actual pair kernel: the common
degenerating geometric frequency is retained, including zero corner outputs. -/
open MeasureTheory Set
namespace Resonance.NormalizedParameterAlgebra
noncomputable section
set_option maxHeartbeats 1000000
open ResonantMeasure WeightedJointMeasure Thermodynamics CollisionFrequency

theorem two_product_difference {a b c d L δ : ℝ} (hL : 0≤L) (hδ : 0≤δ)
    (ha : |a|≤L) (hd : |d|≤L) (hac : |a-c|≤δ) (hbd : |b-d|≤δ) :
    |a*b-c*d|≤2*L*δ := by
  calc
    _ = |a*(b-d)+(a-c)*d| := by congr 1; ring
    _ ≤ |a*(b-d)|+|(a-c)*d| := abs_add_le _ _
    _ ≤ L*δ+δ*L := by
      rw [abs_mul,abs_mul]
      exact add_le_add (mul_le_mul ha hbd (abs_nonneg _) hL)
        (mul_le_mul hac hd (abs_nonneg _) hδ)
    _ = _ := by ring

def normalDenominator (R : ℝ) (θ : Parameter) (k p : E) : ℝ :=
  profile θ k*profile θ p*lossFrequency R (profile θ) p

theorem compact_denominator_bounds {R : ℝ} (hR : 0≤R) {K : Set Parameter}
    (hK : IsCompact K) (hpos : K⊆positiveDomain R) :
    ∃a C : ℝ,0<a ∧ 0≤C ∧
      (∀θ∈K,∀k∈cube R,∀p∈cube R,a*geometricFrequency R p≤normalDenominator R θ k p) ∧
      ∀θ∈K,∀β∈K,∀k∈cube R,∀p∈cube R,
        |normalDenominator R θ k p-normalDenominator R β k p|≤C*‖θ-β‖*geometricFrequency R p := by
  obtain ⟨m,M,Cp,hm,hM,hCp,hb,hd⟩ := ProfileParameterBounds.compact_profile_lipschitz hR hK hpos
  obtain ⟨a,b,Cν,ha,hb0,hCν,hν,hνd⟩ := FrequencyParameterBounds.compact_loss_difference_bound hR hK hpos
  refine ⟨m^2*a,2*M*Cp*b+M^2*Cν,mul_pos (pow_pos hm 2) ha,by positivity,?_,?_⟩
  · intro θ hθ k hk p hp
    have hprod : m^2≤profile θ k*profile θ p := by
      simpa only [pow_two] using mul_le_mul (hb θ hθ k hk).1 (hb θ hθ p hp).1
        hm.le (profile_pos (hpos hθ) hk).le
    calc
      _ = m^2*(a*geometricFrequency R p) := by ring
      _ ≤ _ := mul_le_mul hprod (hν θ hθ p hp).1
        (mul_nonneg ha.le (geometricFrequency_nonnegative R p))
        (mul_nonneg (profile_pos (hpos hθ) hk).le (profile_pos (hpos hθ) hp).le)
  · intro θ hθ β hβ k hk p hp
    have hg := geometricFrequency_nonnegative R p
    have hνθ : 0≤lossFrequency R (profile θ) p :=
      (mul_nonneg ha.le hg).trans (hν θ hθ p hp).1
    have hprodβ : |profile β k*profile β p|≤M^2 := by
      rw [abs_mul,abs_of_pos (profile_pos (hpos hβ) hk),abs_of_pos (profile_pos (hpos hβ) hp)]
      simpa only [pow_two] using mul_le_mul (hb β hβ k hk).2 (hb β hβ p hp).2
        (profile_pos (hpos hβ) hp).le hM.le
    have hprod : |profile θ k*profile θ p-profile β k*profile β p|≤2*M*(Cp*‖θ-β‖) :=
      two_product_difference hM.le (mul_nonneg hCp (norm_nonneg _))
        (by rw [abs_of_pos (profile_pos (hpos hθ) hk)]; exact (hb θ hθ k hk).2)
        (by rw [abs_of_pos (profile_pos (hpos hβ) hp)]; exact (hb β hβ p hp).2)
        (hd θ hθ β hβ k hk) (hd θ hθ β hβ p hp)
    have hνabs : |lossFrequency R (profile θ) p|≤b*geometricFrequency R p := by
      rw [abs_of_nonneg hνθ]
      exact (hν θ hθ p hp).2
    calc
      _ = |(profile θ k*profile θ p-profile β k*profile β p)*lossFrequency R (profile θ) p+
          (profile β k*profile β p)*(lossFrequency R (profile θ) p-lossFrequency R (profile β) p)| := by
        unfold normalDenominator
        congr 1
        ring
      _ ≤ |(profile θ k*profile θ p-profile β k*profile β p)*lossFrequency R (profile θ) p|+
          |(profile β k*profile β p)*(lossFrequency R (profile θ) p-lossFrequency R (profile β) p)| :=
        abs_add_le _ _
      _ ≤ (2*M*(Cp*‖θ-β‖))*(b*geometricFrequency R p)+
          M^2*(Cν*‖θ-β‖*geometricFrequency R p) := by
        rw [abs_mul,abs_mul]
        exact add_le_add (mul_le_mul hprod hνabs (abs_nonneg _) (by positivity))
          (mul_le_mul hprodβ (hνd θ hθ β hβ p hp) (abs_nonneg _) (sq_nonneg _))
      _ = _ := by ring

theorem quotient_difference_bound {a b A r s : ℝ} (hA : 0<A) (ha : A≤a) (hb : A≤b) :
    |r/a-s/b|≤|r-s|/A+|s| * |a-b|/A^2 := by
  have ha0 : 0<a := hA.trans_le ha
  have hb0 : 0<b := hA.trans_le hb
  have hprod : A^2≤a*b := by
    simpa only [pow_two] using mul_le_mul ha hb hA.le ha0.le
  calc
    _ = |(r-s)/a+s*(b-a)/(a*b)| := by
      congr 1
      field_simp
      ring
    _ ≤ |(r-s)/a|+|s*(b-a)/(a*b)| := abs_add_le _ _
    _ = |r-s| * a⁻¹+(|s| * |a-b|)*(a*b)⁻¹ := by
      rw [abs_div,abs_div,abs_mul,abs_of_pos ha0,abs_of_pos (mul_pos ha0 hb0),abs_sub_comm b a]
      simp only [div_eq_mul_inv]
    _ ≤ |r-s| * A⁻¹+(|s| * |a-b|)*(A^2)⁻¹ := by
      exact add_le_add (mul_le_mul_of_nonneg_left (inv_anti₀ hA ha) (abs_nonneg _))
        (mul_le_mul_of_nonneg_left (inv_anti₀ (pow_pos hA 2) hprod)
          (mul_nonneg (abs_nonneg _) (abs_nonneg _)))
    _ = _ := by simp only [div_eq_mul_inv]

theorem weighted_quotient_difference {a b A r s g t δ Cr Br Cd : ℝ}
    (hA : 0<A) (hg : 0<g) (ht : 0≤t) (_hδ : 0≤δ)
    (_hCr : 0≤Cr) (hBr : 0≤Br) (_hCd : 0≤Cd)
    (ha : A*g≤a) (hb : A*g≤b)
    (hrs : |r-s|≤Cr*δ*t) (hs : |s|≤Br*t) (hab : |a-b|≤Cd*δ*g) :
    |r/a-s/b|≤(Cr/A+Br*Cd/A^2)*δ*(t/g) := by
  have he := quotient_difference_bound (mul_pos hA hg) ha hb (r:=r) (s:=s)
  calc
    _ ≤ |r-s|/(A*g)+|s| * |a-b|/(A*g)^2 := he
    _ ≤ (Cr*δ*t)/(A*g)+(Br*t)*(Cd*δ*g)/(A*g)^2 := by
      exact add_le_add (div_le_div_of_nonneg_right hrs (mul_nonneg hA.le hg.le))
        (div_le_div_of_nonneg_right
          (mul_le_mul hs hab (abs_nonneg _) (mul_nonneg hBr ht)) (sq_nonneg _))
    _ = _ := by field_simp

end
end Resonance.NormalizedParameterAlgebra
