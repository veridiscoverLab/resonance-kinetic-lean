import Resonance.OnsagerGradientPolynomial
import Mathlib.LinearAlgebra.Matrix.Rank

/-! Eight explicit effective gradient coordinates, with a proved right
inverse. This supplies exact dimensions for the analytic Onsager kernel. -/
open scoped BigOperators
namespace Resonance.EffectiveGradientSpace
noncomputable section
set_option maxHeartbeats 800000
open ActualOnsagerTensor OnsagerGradientPolynomial

def observation (ξ : Index→ℝ) : Fin 8→ℝ :=
  ![ξ (0,4),ξ (1,4),ξ (2,4),
    ξ (0,1)-ξ (1,2),ξ (1,2)-ξ (2,3),
    ξ (0,2)+ξ (1,1),ξ (0,3)+ξ (2,1),ξ (1,3)+ξ (2,2)]

def observationLinear : (Index→ℝ)→ₗ[ℝ](Fin 8→ℝ) where
  toFun := observation
  map_add' := by
    intro ξ ζ
    funext i
    fin_cases i <;> simp [observation] <;> ring
  map_smul' := by
    intro c ξ
    funext i
    fin_cases i <;> simp [observation,smul_eq_mul] <;> ring

def reconstruction (p : Fin 8→ℝ) : Index→ℝ :=
  gradient (fun _=>0) !![p 3+p 4,p 5,p 6;0,p 4,p 7;0,0,0] ![p 0,p 1,p 2]

theorem observation_reconstruction (p : Fin 8→ℝ) : observation (reconstruction p)=p := by
  funext i
  fin_cases i <;> simp [observation,reconstruction,OnsagerGradientPolynomial.gradient]

theorem observation_surjective : Function.Surjective observationLinear :=
  fun p=>⟨reconstruction p,observation_reconstruction p⟩

theorem observation_gradient_zero_iff (a h : Fin 3→ℝ) (B : Fin 3→Fin 3→ℝ) :
    observation (gradient a B h)=0 ↔ OnsagerPolynomial.nullDirections h B := by
  constructor
  · intro hz
    have h0 := congrFun hz 0
    have h1 := congrFun hz 1
    have h2 := congrFun hz 2
    have h3 := congrFun hz 3
    have h4 := congrFun hz 4
    have h5 := congrFun hz 5
    have h6 := congrFun hz 6
    have h7 := congrFun hz 7
    simp [observation,OnsagerGradientPolynomial.gradient] at h0 h1 h2 h3 h4 h5 h6 h7
    refine ⟨?_,sub_eq_zero.mp h3,sub_eq_zero.mp h4,h5,h6,h7⟩
    intro i
    fin_cases i
    · exact h0
    · exact h1
    · exact h2
  · rintro ⟨hh,h00,h11,h01,h02,h12⟩
    funext i
    fin_cases i <;> simp [observation,OnsagerGradientPolynomial.gradient,hh,h00,h11,h01,h02,h12]

theorem ambient_finrank : Module.finrank ℝ (Index→ℝ)=15 := by simp [Index]

theorem effective_finrank : Module.finrank ℝ observationLinear.range=8 := by
  rw [LinearMap.range_eq_top.mpr observation_surjective]
  simp

theorem kernel_finrank : Module.finrank ℝ observationLinear.ker=7 := by
  have hh := observationLinear.finrank_range_add_finrank_ker
  rw [effective_finrank,ambient_finrank] at hh
  omega

end
end Resonance.EffectiveGradientSpace
