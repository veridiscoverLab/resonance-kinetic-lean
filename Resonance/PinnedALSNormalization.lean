import Resonance.PinnedRJProfile
import Resonance.PinnedOperator

/-! Exact ALS prefactor and thermal scaling in the original angular
probability-Haar/coarea convention fixed by PinnedMeasureNormalization. -/
open Set MeasureTheory
namespace Resonance.PinnedALSNormalization
noncomputable section
open PinnedPeriodicity PinnedEndToEnd PinnedClassificationFinal PinnedMaximalDifference
open PinnedPhysicalMultiplier PinnedRJProfile PinnedClosedForm
local notation "Circle" => PinnedPeriodicity.Circle
local instance periodPositive : Fact (0 < period) := ⟨period_pos⟩

def alsGamma : ℝ := 9*Real.pi/4
def alsWeight (d : ℝ) (k : FourCircle) : ℝ := ∏ i,(circleDispersion d (k i))⁻¹^2

theorem alsGamma_positive : 0 < alsGamma := by unfold alsGamma; positivity
theorem als_form_prefactor : alsGamma/4=9*Real.pi/16 := by unfold alsGamma; ring

def thermalParameter {d : ℝ} (hd0 : 0 < d) (hdU : d < 1/2)
    {β : ℝ} (hβ : 0 < β) : positiveDomain d :=
  ⟨(0,β),fun x => by
    change 0 < 0+β*circleDispersion d x
    simpa using mul_pos hβ (dispersion_positive hd0 hdU x)⟩

theorem thermal_profile {d : ℝ} (hd0 : 0 < d) (hdU : d < 1/2)
    {β : ℝ} (hβ : 0 < β) (x : Circle) :
    profile hd0 hdU (thermalParameter hd0 hdU hβ) x=(β*circleDispersion d x)⁻¹ := by
  simp [profile,thermalParameter]

theorem thermal_weight {d : ℝ} (hd0 : 0 < d) (hdU : d < 1/2)
    {β : ℝ} (hβ : 0 < β) (k : FourCircle) :
    physicalWeight d (profile hd0 hdU (thermalParameter hd0 hdU hβ)) k=β⁻¹^4*alsWeight d k := by
  have he (i : Fin 4) : profile hd0 hdU (thermalParameter hd0 hdU hβ) (k i)/circleDispersion d (k i)=
      β⁻¹*(circleDispersion d (k i))⁻¹^2 := by
    rw [thermal_profile]
    simp only [mul_inv_rev,div_eq_mul_inv,pow_two]
    ring
  unfold physicalWeight
  simp_rw [he]
  rw [Finset.prod_mul_distrib]
  simp only [Finset.prod_const,Finset.card_univ,Fintype.card_fin,alsWeight]

theorem original_ALS_form {d : ℝ} (hd0 : 0 < d) (hdU : d < 1/2)
    (u v : FormDomain hd0 hdU (alsWeight d)) :
    PinnedOperator.paperForm hd0 hdU (alsWeight d) alsGamma u v =
      (9*(Real.pi : ℂ)/16)*∫ k,difference (u : Source) k*
        star (difference (v : Source) k) ∂weightedCoarea d (alsWeight d) := by
  rw [PinnedOperator.paperForm_integral]
  congr 1
  simp only [alsGamma,Complex.ofReal_div,Complex.ofReal_mul,Complex.ofReal_ofNat]
  ring

end
end Resonance.PinnedALSNormalization
