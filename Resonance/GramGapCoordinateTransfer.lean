import Resonance.GramGapTransport

/-! A proved square-gap transfer through bounded inverse coordinates. -/
namespace Resonance.GramGapCoordinateTransfer
noncomputable section
variable {H H₀ J : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [NormedAddCommGroup H₀] [InnerProductSpace ℝ H₀] [CompleteSpace H₀]
  [NormedAddCommGroup J] [InnerProductSpace ℝ J]

theorem transfer_square_gap (T₀ : H₀→L[ℝ]J) (E : H→L[ℝ]H₀) (B : H₀→L[ℝ]H)
    {a δ : ℝ} (hδ : 0≤δ)
    (hB : ∀v,‖B v‖≤a*‖v‖) (hBE : ∀v,B (E v)=v) (hEB : ∀v,E (B v)=v)
    (hgap : ∀v,δ*‖v-T₀.ker.starProjection v‖^2≤‖T₀ v‖^2) (f : H) :
    (δ/(1+a^2))*‖f-(T₀.comp E).ker.starProjection f‖^2≤‖T₀ (E f)‖^2 := by
  let g : H₀ := T₀.ker.starProjection (E f)
  have hg : B g∈(T₀.comp E).ker := by
    change T₀ (E (B g))=0
    rw [hEB]
    exact T₀.ker.starProjection_apply_mem (E f)
  have hd : ‖f-(T₀.comp E).ker.starProjection f‖≤a*‖E f-g‖ := by
    apply (GramGapTransport.projection_residual_le (T₀.comp E) f (B g) hg).trans
    have he : f-B g=B (E f-g) := by rw [map_sub,hBE]
    rw [he]
    exact hB _
  have hs := pow_le_pow_left₀ (norm_nonneg _) hd 2
  rw [mul_pow] at hs
  have hmain : δ*‖f-(T₀.comp E).ker.starProjection f‖^2≤(1+a^2)*‖T₀ (E f)‖^2 := by
    calc
      _ ≤ δ*(a^2*‖E f-g‖^2) := mul_le_mul_of_nonneg_left hs hδ
      _ = a^2*(δ*‖E f-g‖^2) := by ring
      _ ≤ a^2*‖T₀ (E f)‖^2 := mul_le_mul_of_nonneg_left (hgap (E f)) (sq_nonneg _)
      _ ≤ _ := by nlinarith [sq_nonneg ‖T₀ (E f)‖]
  have hp : 0<1+a^2 := by positivity
  rw [div_mul_eq_mul_div,div_le_iff₀ hp]
  simpa only [mul_comm (1+a^2)] using hmain

end
end Resonance.GramGapCoordinateTransfer
