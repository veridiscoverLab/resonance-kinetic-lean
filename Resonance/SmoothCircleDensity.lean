import Resonance.PinnedClassificationFinal
import Mathlib.Analysis.Fourier.AddCircle

/-! Smooth periodic representatives are dense in the paper's actual
probability-Haar L² space.  This is an approximation statement, not an
assertion that smooth functions have finite full-coarea energy.  That
separate geometric domain statement is needed to infer a dense form
domain.  The proof uses the actual Fourier characters and their proved
Stone--Weierstrass density, rather than assuming a smooth core. -/
open Real MeasureTheory Set Filter
open scoped ENNReal NNReal Topology ContDiff
namespace Resonance.SmoothCircleDensity
noncomputable section
open Resonance.PinnedPeriodicity Resonance.PinnedClassificationFinal
local instance periodPositive : Fact (0<period) := ⟨period_pos⟩

abbrev CircleL2 := Lp ℂ 2 circleHaar

def smoothContinuous : Submodule ℂ C(PinnedPeriodicity.Circle,ℂ) where
  carrier := {f | ContDiff ℝ ∞ (periodicLift f)}
  zero_mem' := by
    change ContDiff ℝ ∞ (fun _x:ℝ=>(0:ℂ))
    exact contDiff_const
  add_mem' := by
    intro f g hf hg
    change ContDiff ℝ ∞ (periodicLift f) at hf
    change ContDiff ℝ ∞ (periodicLift g) at hg
    change ContDiff ℝ ∞ (fun x=>periodicLift f x+periodicLift g x)
    exact hf.add hg
  smul_mem' := by
    intro c f hf
    change ContDiff ℝ ∞ (periodicLift f) at hf
    change ContDiff ℝ ∞ (fun x=>c*periodicLift f x)
    exact contDiff_const.mul hf

def smoothVectors : Submodule ℂ CircleL2 :=
  smoothContinuous.map (ContinuousMap.toLp (E:=ℂ) 2 circleHaar ℂ).toLinearMap

theorem fourier_lift_smooth (n:ℤ) :
    ContDiff ℝ ∞ (periodicLift (@fourier period n)) := by
  have he : periodicLift (@fourier period n)=
      fun x:ℝ=>Complex.exp (2*π*Complex.I*n*(x:ℂ)/period) := by
    funext x
    exact fourier_coe_apply
  rw [he]
  exact Complex.contDiff_exp.comp
    ((contDiff_const.mul Complex.ofRealCLM.contDiff).div_const _)

theorem fourier_mem_smoothContinuous (n:ℤ) :
    @fourier period n∈smoothContinuous := fourier_lift_smooth n

theorem span_fourier_actual_L2_dense :
    (Submodule.span ℂ (range (fun n:ℤ=>
      ContinuousMap.toLp (E:=ℂ) 2 circleHaar ℂ (@fourier period n)))).topologicalClosure=⊤ := by
  convert
    (ContinuousMap.toLp_denseRange ℂ circleHaar ℂ (p:=2) (by norm_num)).topologicalClosure_map_submodule
      (@span_fourier_closure_eq_top period periodPositive) using 1
  rw [Submodule.map_span]
  rw [range_comp']
  simp only [ContinuousLinearMap.coe_coe]

theorem smoothVectors_closure_eq_top : smoothVectors.topologicalClosure=⊤ := by
  have hspan : Submodule.span ℂ (range (fun n:ℤ=>
      ContinuousMap.toLp (E:=ℂ) 2 circleHaar ℂ (@fourier period n))) ≤ smoothVectors := by
    apply Submodule.span_le.mpr
    rintro _ ⟨n,rfl⟩
    exact ⟨fourier n,fourier_mem_smoothContinuous n,rfl⟩
  apply top_unique
  rw [←span_fourier_actual_L2_dense]
  exact Submodule.topologicalClosure_mono hspan

/-- Every physical L² equivalence class admits arbitrarily close smooth
periodic representatives, with the same normalized circle Haar measure. -/
theorem exists_smooth_periodic_approximation (u:CircleL2) {ε:ℝ} (hε:0<ε) :
    ∃F:C(PinnedPeriodicity.Circle,ℂ),
      ContDiff ℝ ∞ (periodicLift F) ∧ Function.Periodic (periodicLift F) period ∧
      dist (ContinuousMap.toLp (E:=ℂ) 2 circleHaar ℂ F) u<ε := by
  have hu : u∈smoothVectors.topologicalClosure := by rw [smoothVectors_closure_eq_top]; trivial
  have hc : u∈closure (smoothVectors:Set CircleL2) := hu
  obtain ⟨v,hv,hd⟩ := Metric.mem_closure_iff.mp hc ε hε
  obtain ⟨F,hF,rfl⟩ := hv
  exact ⟨F,hF,periodicLift_periodic F,by simpa only [dist_comm] using hd⟩

/-- A sequence version convenient for passing to the maximal closed form
domain after its independent smooth finite-energy theorem is available. -/
theorem exists_smooth_periodic_sequence (u:CircleL2) :
    ∃F:ℕ→C(PinnedPeriodicity.Circle,ℂ),
      (∀n,ContDiff ℝ ∞ (periodicLift (F n))) ∧
      (∀n,Function.Periodic (periodicLift (F n)) period) ∧
      Tendsto (fun n=>ContinuousMap.toLp (E:=ℂ) 2 circleHaar ℂ (F n)) atTop (𝓝 u) := by
  have he (n:ℕ) := exists_smooth_periodic_approximation u
    (ε:=1/((n:ℝ)+1)) (by positivity)
  choose F hF hp hdist using he
  refine ⟨F,hF,hp,?_⟩
  apply tendsto_iff_dist_tendsto_zero.mpr
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    tendsto_one_div_add_atTop_nhds_zero_nat (fun _=>dist_nonneg) (fun n=>(hdist n).le)

end
end Resonance.SmoothCircleDensity
