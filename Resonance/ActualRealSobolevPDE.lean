import Resonance.ActualSobolevPDE
import Resonance.ActualSpatialPolynomials
import Resonance.ActualSobolevReality
import Resonance.ActualSobolevDecay

/-! One original real five-moment solution, in every real Sobolev order,
with strong H^(s-2) PDE and the compact-parameter decay on all five mean-zero
components. Real data, initial trace, spatial derivatives, and decay belong
to the same constructed evolution. -/
open Set
namespace Resonance.ActualRealSobolevPDE
noncomputable section
open Thermodynamics MatrixHilbertDictionary ActualSobolevSpace ActualSobolevSemigroup
open ActualSobolevDifferentiation ActualSobolevMatrixAction ActualSobolevInclusion
open ActualSpatialDifferentials ActualSpatialMatrixSymbols ActualSobolevReality

theorem original_real_complete_pde {R : ℝ} (hR : 0<R) {θ : Parameter}
    (hθ : θ∈positiveDomain R) {c : ℝ} (hc : 0<c) (s : ℝ)
    (v : Sobolev s) (hv : IsReal hR hθ s v) :
    Continuous (trajectory hR hθ hc s v) ∧ trajectory hR hθ hc s v 0=v ∧
      (∀t:ℝ,0≤t→IsReal hR hθ s (trajectory hR hθ hc s v t)) ∧
      ∀t:ℝ,0≤t→
        HasDerivWithinAt (fun r=>inclusion s (trajectory hR hθ hc s v r))
          (differential hR hθ hc s (trajectory hR hθ hc s v t)) (Ici 0) t ∧
        action hR hθ (s-2) (gramMatrix R θ)
            (differential hR hθ hc s (trajectory hR hθ hc s v t))+
          ∑j:Fin 3,action hR hθ (s-2) (EulerCoefficients.fluxMatrix R j θ)
            (first s j (trajectory hR hθ hc s v t))=
          (c⁻¹:ℂ) • ∑i:Fin 3,∑j:Fin 3,action hR hθ (s-2) (block hR hθ i j)
            (second s i j (trajectory hR hθ hc s v t)) := by
  refine ⟨trajectory_continuous hR hθ hc s v,?_,?_,?_⟩
  · simp only [trajectory,Real.toNNReal_zero,evolution_zero,ContinuousLinearMap.one_apply]
  · intro t _
    exact evolution_preserves_real hR hθ hc s (Real.toNNReal t) v hv
  · intro t ht
    exact ActualSobolevPDE.original_evolution_pde hR hθ hc s v ht

theorem original_real_complete_decay {R : ℝ} (hR : 0<R) {K : Set Parameter}
    (hK : IsCompact K) (hpos : K⊆positiveDomain R) :
    ∃a : ℝ,0<a ∧ ∀θ:K,∀c:ℝ,∀hc:1≤c,∀s:ℝ,∀v:Sobolev s,
      IsReal hR (hpos θ.property) s v→coefficient hR (hpos θ.property) s v 0=0→
      ∀t:ℝ,0≤t→
        IsReal hR (hpos θ.property) s
          (trajectory hR (hpos θ.property) (lt_of_lt_of_le zero_lt_one hc) s v t) ∧
        ‖trajectory hR (hpos θ.property) (lt_of_lt_of_le zero_lt_one hc) s v t‖≤
          Real.sqrt 3*Real.exp (-a*t/c)*‖v‖ := by
  obtain ⟨a,ha,hd⟩ := ActualSobolevDecay.original_torus_sobolev_decay hR hK hpos
  refine ⟨a,ha,?_⟩
  intro θ c hc s v hv hzero t ht
  refine ⟨evolution_preserves_real hR (hpos θ.property)
    (lt_of_lt_of_le zero_lt_one hc) s (Real.toNNReal t) v hv,?_⟩
  simpa only [trajectory,Real.coe_toNNReal t ht] using hd θ c hc s (Real.toNNReal t) v hzero

end
end Resonance.ActualRealSobolevPDE
