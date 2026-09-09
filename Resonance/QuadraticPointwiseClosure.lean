import Resonance.QuadraticCollisionInvariants
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-! The five-dimensional polynomial family is closed in pointwise convergence
on any one common set. This preserves the actual almost-everywhere convergence
set, without requiring uniform convergence of mollifications. -/
open Set Filter
open scoped Topology

namespace Resonance.QuadraticPointwiseClosure
noncomputable section
open ResonantMeasure QuadraticCollisionInvariants

abbrev Coefficients := ℝ × (E →L[ℝ] ℝ) × ℝ

def evaluate (c : Coefficients) (x : E) : ℝ := c.1+c.2.1 x+c.2.2*‖x‖^2

def evaluationMap (S : Set E) : Coefficients →ₗ[ℝ] (S → ℝ) where
  toFun c x := evaluate c x
  map_add' a b := by ext x; simp [evaluate]; ring
  map_smul' a b := by ext x; simp [evaluate]; ring

theorem polynomial_range_closed (S : Set E) :
    IsClosed (Set.range (fun c : Coefficients => fun x : S => evaluate c x)) := by
  change IsClosed (LinearMap.range (evaluationMap S) : Set (S → ℝ))
  exact (LinearMap.range (evaluationMap S)).closed_of_finiteDimensional

theorem pointwise_limit_polynomial (S : Set E) (c : ℕ → Coefficients) (f : E → ℝ)
    (hc : ∀ x∈S, Tendsto (fun n => evaluate (c n) x) atTop (𝓝 (f x))) :
    ∃ b : Coefficients, ∀ x∈S, f x = evaluate b x := by
  have ht : Tendsto (fun n => fun x : S => evaluate (c n) x) atTop
      (𝓝 (fun x : S => f x)) :=
    tendsto_pi_nhds.mpr (fun x => hc x x.property)
  have hm := (polynomial_range_closed S).mem_of_tendsto ht
    (Eventually.of_forall (fun n => ⟨c n,rfl⟩))
  obtain ⟨b,hb⟩ := hm
  exact ⟨b,fun x hx => (congrFun hb ⟨x,hx⟩).symm⟩

end
end Resonance.QuadraticPointwiseClosure
