import Resonance.CornerConvolutionBounds

/-! The winning coordinate supplies a true lower rectangle in the full
original nonnegative convolution. -/
open Real Set MeasureTheory
open scoped ENNReal Topology
namespace Resonance.CornerConvolutionLower
noncomputable section
set_option maxHeartbeats 600000
open Resonance.CornerConvolution Resonance.CornerConvolutionBounds
open Resonance.AxisProductDensity Resonance.TriangleProductDensity
open Resonance.CornerDensityBounds

theorem positive_density_lower {d e s:ℝ} (hd0:0≤d) (hde:d≤e)
    (he0:0<e) (he1:e≤(1:ℝ)/256) (hs0:0<s) (hse:s≤e) :
    ENNReal.ofReal (Real.log (1/e)/2)≤axisDensity d s := by
  have hb0 : (1:ℝ)/2≤1-d := by linarith
  have hb1 : 1-d≤1 := by linarith
  have ht := (small_triangle_density_bounds hb0 hb1 hs0 (hse.trans he1)).1
  have hlog := Real.log_le_log (by positivity:0<1/e)
    (one_div_le_one_div_of_le hs0 hse)
  have hl : ENNReal.ofReal (Real.log (1/e)/2)≤triangleDensity (1-d) s :=
    (ENNReal.ofReal_le_ofReal (by linarith)).trans ht
  rw [axis_density_positive hs0]
  exact hl.trans le_add_self

theorem third_max_lower (d:Fin 3→ℝ) {e:ℝ}
    (hd0:∀i,0≤d i) (hde:∀i,d i≤e) (hmax:d 2=e)
    (he0:0<e) (he1:e≤(1:ℝ)/256) :
    (ENNReal.ofReal (Real.log (1/e)/2))^2*(2*ENNReal.ofReal (Real.log 2))*
      (ENNReal.ofReal (e/48))^2≤ sumDensity d 0 := by
  let I : Set ℝ := Ioo (e/16) (e/12)
  let K : ℝ≥0∞ := (ENNReal.ofReal (Real.log (1/e)/2))^2*
    (2*ENNReal.ofReal (Real.log 2))
  have hpoint {s t:ℝ} (hs:s∈I) (ht:t∈I) :
      K≤axisDensity (d 0) s*axisDensity (d 1) t*axisDensity (d 2) (0-s-t) := by
    have hs0 : 0<s := by rcases hs with ⟨hs,_⟩; linarith
    have ht0 : 0<t := by rcases ht with ⟨ht,_⟩; linarith
    have hse : s≤e := by rcases hs with ⟨_,hs⟩; linarith
    have hte : t≤e := by rcases ht with ⟨_,ht⟩; linarith
    have h0 := positive_density_lower (hd0 0) (hde 0) he0 he1 hs0 hse
    have h1 := positive_density_lower (hd0 1) (hde 1) he0 he1 ht0 hte
    have hsum : s+t≤e/4 := by rcases hs with ⟨_,hs⟩; rcases ht with ⟨_,ht⟩; linarith
    have hn := rectangle_density_lower_on_corner_band he0 (by linarith:e≤(1:ℝ)/2)
      (add_pos hs0 ht0) hsum
    have h2 : 2*ENNReal.ofReal (Real.log 2)≤axisDensity (d 2) (0-s-t) := by
      rw [hmax,show 0-s-t= -(s+t) by ring,axis_density_negative (add_pos hs0 ht0)]
      exact mul_le_mul_right hn 2
    simpa only [K,pow_two] using (mul_le_mul' (mul_le_mul' h0 h1) h2)
  have houter : (∫⁻s in I,∫⁻t in I,K)≤
      ∫⁻s in I,∫⁻t in I,axisDensity (d 0) s*axisDensity (d 1) t*axisDensity (d 2) (0-s-t) := by
    apply lintegral_mono_ae
    filter_upwards [ae_restrict_mem (show MeasurableSet I from measurableSet_Ioo)] with s hs
    apply lintegral_mono_ae
    filter_upwards [ae_restrict_mem (show MeasurableSet I from measurableSet_Ioo)] with t ht
    exact hpoint hs ht
  have hmass : (volume:Measure ℝ) I=ENNReal.ofReal (e/48) := by
    dsimp [I]
    rw [Real.volume_Ioo]
    congr 1
    ring
  have hleft : (∫⁻s in I,∫⁻t in I,K)=K*(ENNReal.ofReal (e/48))^2 := by
    simp only [lintegral_const,Measure.restrict_apply_univ,hmass]
    ring
  rw [hleft] at houter
  refine houter.trans ?_
  apply le_trans (lintegral_mono (fun s=>setLIntegral_le_lintegral I _))
  exact setLIntegral_le_lintegral I _

end
end Resonance.CornerConvolutionLower
