import Resonance.PhysicalFourierCharacters
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-! Actual derivatives of the original period-2pi characters on their
real-coordinate lifts. These identify the signs and all mixed spatial slots. -/
namespace Resonance.PhysicalFourierDerivatives
noncomputable section
open PhysicalScalarFourier PhysicalFourierCharacters FreeTransport

def phase (n : Frequency) (X : Fin 3→ℝ) : ℂ := ∑j:Fin 3,(n j:ℂ)*(X j:ℂ)
def liftedCharacter (n : Frequency) (X : Fin 3→ℝ) : ℂ := Complex.exp (Complex.I*phase n X)
def axisShift (X : Fin 3→ℝ) (j : Fin 3) (h : ℝ) : Fin 3→ℝ := X+Pi.single j h

theorem liftedCharacter_original (n : Frequency) (X : Fin 3→ℝ) :
    liftedCharacter n X=character n (fun j=>(X j:AddCircle period)) := by
  rw [character_real,liftedCharacter,phase,Finset.mul_sum,Complex.exp_sum]
  apply Finset.prod_congr rfl
  intro j _
  congr 1
  ring

theorem axisShift_zero (X : Fin 3→ℝ) (j : Fin 3) : axisShift X j 0=X := by
  simp [axisShift]

theorem phase_axis (n : Frequency) (X : Fin 3→ℝ) (j : Fin 3) (h : ℝ) :
    phase n (axisShift X j h)=phase n X+(n j:ℂ)*(h:ℂ) := by
  classical
  simp only [phase,axisShift,Pi.add_apply,Complex.ofReal_add,mul_add,Finset.sum_add_distrib]
  congr 1
  simp [Pi.single_apply,apply_ite]

theorem liftedCharacter_axis_hasDerivAt (n : Frequency) (X : Fin 3→ℝ)
    (j : Fin 3) (a : ℝ) :
    HasDerivAt (fun h=>liftedCharacter n (axisShift X j h))
      ((Complex.I*(n j:ℂ))*liftedCharacter n (axisShift X j a)) a := by
  have hp : HasDerivAt (fun h=>phase n (axisShift X j h)) (n j:ℂ) a := by
    have hi : HasDerivAt (fun h:ℝ=>(h:ℂ)) (1:ℂ) a := Complex.ofRealCLM.hasDerivAt
    simpa only [phase_axis,mul_one] using
      (hi.const_mul (n j:ℂ)).const_add (phase n X)
  have hh := (hp.const_mul Complex.I).cexp
  convert hh using 1
  unfold liftedCharacter
  ring

def axisDerivative (f : (Fin 3→ℝ)→ℂ) (j : Fin 3) (X : Fin 3→ℝ) : ℂ :=
  deriv (fun h=>f (axisShift X j h)) 0

theorem liftedCharacter_first (n : Frequency) (X : Fin 3→ℝ) (j : Fin 3) :
    axisDerivative (liftedCharacter n) j X=(Complex.I*(n j:ℂ))*liftedCharacter n X := by
  simpa only [axisDerivative,axisShift_zero] using (liftedCharacter_axis_hasDerivAt n X j 0).deriv

theorem liftedCharacter_second (n : Frequency) (X : Fin 3→ℝ) (i j : Fin 3) :
    axisDerivative (fun Y=>axisDerivative (liftedCharacter n) j Y) i X=
      -((n i:ℂ)*(n j:ℂ))*liftedCharacter n X := by
  have hh := (liftedCharacter_axis_hasDerivAt n X i 0).const_mul (Complex.I*(n j:ℂ))
  have he := hh.deriv
  simp only [axisShift_zero] at he
  simp only [liftedCharacter_first]
  change deriv (fun h=>(Complex.I*(n j:ℂ))*liftedCharacter n (axisShift X i h)) 0=_
  rw [he]
  have hI := Complex.I_mul_I
  calc
    _ = (Complex.I*Complex.I)*((n i:ℂ)*(n j:ℂ))*liftedCharacter n X := by ring
    _ = _ := by rw [hI]; ring

end
end Resonance.PhysicalFourierDerivatives
