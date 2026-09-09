import Resonance.CompactGramGap

/-! Quantitative transfer of a proved full-form gap through maps which
retain the same kernel and the same full difference. -/
open Set
namespace Resonance.GramGapTransport
noncomputable section
variable {H H₀ J J₀ : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [NormedAddCommGroup H₀] [InnerProductSpace ℝ H₀] [CompleteSpace H₀]
  [NormedAddCommGroup J] [InnerProductSpace ℝ J]
  [NormedAddCommGroup J₀] [InnerProductSpace ℝ J₀]

theorem projection_residual_le (T : H→L[ℝ]J) (f g : H) (hg : g∈T.ker) :
    ‖f-T.ker.starProjection f‖≤‖f-g‖ := by
  have h := T.kerᗮ.norm_starProjection_apply_le (f-g)
  rw [Submodule.starProjection_orthogonal',ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.one_apply,map_sub,T.ker.starProjection_eq_self_iff.mpr hg] at h
  convert h using 1
  congr 1
  abel

theorem projected_norm_gap (T : H→L[ℝ]J) {γ : ℝ}
    (hgap : ∀v : H,v∈T.kerᗮ → γ*‖v‖≤‖T v‖) (f : H) :
    γ*‖f-T.ker.starProjection f‖≤‖T f‖ := by
  have h := hgap (f-T.ker.starProjection f) (T.ker.sub_starProjection_mem_orthogonal f)
  have hz : T (T.ker.starProjection f)=0 := T.ker.starProjection_apply_mem f
  simpa only [map_sub,hz,sub_zero] using h

theorem transfer_norm_gap (T : H→L[ℝ]J) (T₀ : H₀→L[ℝ]J₀)
    (E : H→L[ℝ]H₀) (B : H₀→L[ℝ]H) (F : J→L[ℝ]J₀)
    {a b γ : ℝ} (ha : 0≤a) (hb : 0≤b) (hγ : 0<γ)
    (hB : ∀v,‖B v‖≤a*‖v‖) (hF : ∀v,‖F v‖≤b*‖v‖)
    (hBE : ∀v,B (E v)=v) (hT : ∀v,T₀ (E v)=F (T v))
    (hker : ∀v∈T₀.ker,B v∈T.ker)
    (hgap : ∀v : H₀,v∈T₀.kerᗮ → γ*‖v‖≤‖T₀ v‖) (f : H) :
    (γ/(1+a*b))*‖f-T.ker.starProjection f‖≤‖T f‖ := by
  let g : H₀ := T₀.ker.starProjection (E f)
  have hg : g∈T₀.ker := T₀.ker.starProjection_apply_mem (E f)
  have hdist : ‖f-T.ker.starProjection f‖≤a*‖E f-g‖ := by
    apply (projection_residual_le T f (B g) (hker g hg)).trans
    have he : f-B g=B (E f-g) := by rw [map_sub,hBE]
    rw [he]
    exact hB _
  have hbase := projected_norm_gap T₀ hgap (E f)
  have hdiff : ‖T₀ (E f)‖≤b*‖T f‖ := by rw [hT]; exact hF _
  have hmain : γ*‖f-T.ker.starProjection f‖≤(1+a*b)*‖T f‖ := by
    calc
      _ ≤ γ*(a*‖E f-g‖) := mul_le_mul_of_nonneg_left hdist hγ.le
      _ = a*(γ*‖E f-g‖) := by ring
      _ ≤ a*‖T₀ (E f)‖ := mul_le_mul_of_nonneg_left hbase ha
      _ ≤ a*(b*‖T f‖) := mul_le_mul_of_nonneg_left hdiff ha
      _ ≤ _ := by nlinarith [norm_nonneg (T f)]
  have hab : 0<1+a*b := by positivity
  rw [div_mul_eq_mul_div,div_le_iff₀ hab]
  simpa only [mul_comm (1+a*b)] using hmain

end
end Resonance.GramGapTransport
