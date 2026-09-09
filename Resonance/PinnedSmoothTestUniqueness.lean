import Resonance.ContinuousDensityFunctional
import Resonance.SmoothCircleDensity

/-! Smooth periodic tests determine an L¹ density. This uses uniform
Fourier Stone--Weierstrass density, not merely L² density against an L¹
unknown and not a presumed smooth form core. -/
open Set MeasureTheory
open scoped ContDiff
namespace Resonance.PinnedSmoothTestUniqueness
noncomputable section
open PinnedPeriodicity PinnedClassificationFinal SmoothCircleDensity
local instance periodPositive : Fact (0<period) := ⟨period_pos⟩

theorem ae_zero_of_smooth_tests {f : PinnedPeriodicity.Circle→ℂ} (hf : Integrable f circleHaar)
    (h : ∀ψ:C(PinnedPeriodicity.Circle,ℂ),ContDiff ℝ ∞ (periodicLift ψ)→
      (∫x,ψ x*f x∂circleHaar)=0) : f=ᵐ[circleHaar] 0 := by
  let L := ContinuousDensityFunctional.functional circleHaar hf
  have hspan : Submodule.span ℂ (range (@fourier period))≤L.ker := by
    apply Submodule.span_le.mpr
    rintro _ ⟨n,rfl⟩
    exact h (fourier n) (fourier_lift_smooth n)
  have htop : (⊤ : Submodule ℂ C(PinnedPeriodicity.Circle,ℂ))≤L.ker := by
    rw [←span_fourier_closure_eq_top]
    exact Submodule.topologicalClosure_minimal _ hspan L.isClosed_ker
  apply ContinuousTestUniqueness.ae_zero_of_continuous_tests circleHaar hf
  intro ψ
  exact htop (Submodule.mem_top)

end
end Resonance.PinnedSmoothTestUniqueness
