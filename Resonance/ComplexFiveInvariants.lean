import Resonance.FiveInvariantFinal

/-! Complex-valued invariants are classified on the same full measure;
real and imaginary parts are reassembled with their unique coefficients. -/
open Set MeasureTheory Filter

namespace Resonance.ComplexFiveInvariants
noncomputable section
open ResonantMeasure ContinuousCollisionInvariants QuadraticPointwiseClosure FiveInvariantFinal

def invariant (R : ℝ) (f : E → ℂ) : Prop :=
  ∀ᵐ q ∂pairingMeasure R, f (q 0)+f (q 1)=f (q 2)+f (q 3)

abbrev ComplexCoefficients := Coefficients × Coefficients
def evaluateComplex (c : ComplexCoefficients) (x : E) : ℂ :=
  ⟨evaluate c.1 x,evaluate c.2 x⟩

theorem evaluateComplex_five_moments (c : ComplexCoefficients) (x : E) :
    evaluateComplex c x = (⟨c.1.1,c.2.1⟩ : ℂ) +
      (∑ j : Fin 3, (⟨c.1.2.1 (ParallelGradientAlgebra.axisPoint 1 j),
        c.2.2.1 (ParallelGradientAlgebra.axisPoint 1 j)⟩ : ℂ)*(x j : ℂ)) +
      (⟨c.1.2.2,c.2.2.2⟩ : ℂ)*(‖x‖^2 : ℝ) := by
  apply Complex.ext <;> simp [evaluateComplex,evaluate_five_moments,Fin.sum_univ_succ,pow_two]

theorem invariant_real {R : ℝ} {f : E → ℂ} (hf : invariant R f) :
    ContinuousCollisionInvariants.invariant R (fun x => (f x).re) := by
  filter_upwards [hf] with q hq
  simpa only [Complex.add_re] using congrArg Complex.re hq

theorem invariant_imag {R : ℝ} {f : E → ℂ} (hf : invariant R f) :
    ContinuousCollisionInvariants.invariant R (fun x => (f x).im) := by
  filter_upwards [hf] with q hq
  simpa only [Complex.add_im] using congrArg Complex.im hq

theorem original_complex_invariant_unique {R : ℝ} (hR : 0<R) {f : E → ℂ}
    (hfl : LocallyIntegrableOn f (openCube R)) (hf : invariant R f) :
    ∃! c : ComplexCoefficients,
      f =ᵐ[(volume : Measure E).restrict (cube R)] evaluateComplex c := by
  obtain ⟨a,ha,hua⟩ := original_cube_invariant_unique hR
    (Complex.reCLM.locallyIntegrableOn_comp hfl) (invariant_real hf)
  obtain ⟨b,hb,hub⟩ := original_cube_invariant_unique hR
    (Complex.imCLM.locallyIntegrableOn_comp hfl) (invariant_imag hf)
  refine ⟨⟨a,b⟩,?_,?_⟩
  · filter_upwards [ha,hb] with x hx hy
    exact Complex.ext hx hy
  · intro c hc
    apply Prod.ext
    · apply hua
      filter_upwards [hc] with x hx
      exact congrArg Complex.re hx
    · apply hub
      filter_upwards [hc] with x hx
      exact congrArg Complex.im hx

end
end Resonance.ComplexFiveInvariants
