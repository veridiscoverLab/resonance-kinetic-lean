import Resonance.CollisionFrequency

/-! In the same actual quartet, two opposite legs in the same corner
force both adjacent legs into the doubled corner box. The original
fixed-output conditional measure is bounded by that small box fiber. -/
open Real Set MeasureTheory
open scoped ENNReal
namespace Resonance.OppositeCornerBox
noncomputable section
open PlaneCoarea PlaneGlobal CollisionFiber CollisionFrequency
set_option maxHeartbeats 1000000

def upperCorner (R ρ : ℝ) : Set E := {k | ∀j:Fin 3,R-ρ≤k j ∧ k j≤R}

theorem upperCorner_measurable (R ρ : ℝ) : MeasurableSet (upperCorner R ρ) := by
  change MeasurableSet {k:E | ∀j:Fin 3,R-ρ≤k j ∧ k j≤R}
  simp only [setOf_forall]
  apply MeasurableSet.iInter
  intro j
  have hc : Continuous (fun k:E=>k j) := by fun_prop
  exact (isClosed_le continuous_const hc).measurableSet.inter
    (isClosed_le hc continuous_const).measurableSet

def boxCenter (R ρ : ℝ) : E := WithLp.toLp 2 (fun _:Fin 3=>R-ρ)

theorem actual_momentum_small_box {R ρ : ℝ} (hρ : 0≤ρ) (q : FourMomenta)
    (h0 : q 0∈upperCorner R ρ) (h1 : q 1∈upperCorner R ρ)
    (hall : ∀l:Fin 4,q l∈ResonantMeasure.cube R) (hm : q 0+q 1=q 2+q 3) :
    ∀l:Fin 4,q l-boxCenter R ρ∈ResonantMeasure.cube ρ := by
  have hlow : ∀l:Fin 4,∀j:Fin 3,R-2*ρ≤q l j := by
    intro l j
    have hq := congrArg (fun x:E=>x j) hm
    change q 0 j+q 1 j=q 2 j+q 3 j at hq
    have h2 := (abs_le.mp (hall 2 j)).2
    have h3 := (abs_le.mp (hall 3 j)).2
    fin_cases l
    · change R-2*ρ≤q 0 j
      linarith [(h0 j).1]
    · change R-2*ρ≤q 1 j
      linarith [(h1 j).1]
    · change R-2*ρ≤q 2 j
      linarith [(h0 j).1,(h1 j).1]
    · change R-2*ρ≤q 3 j
      linarith [(h0 j).1,(h1 j).1]
  intro l j
  change |q l j-(R-ρ)|≤ρ
  exact abs_le.mpr ⟨by linarith [hlow l j],by linarith [(abs_le.mp (hall l j)).2]⟩

theorem rectangleFour_momentum (k x y : E) :
    rectangleFour k x y 0+rectangleFour k x y 1=
      rectangleFour k x y 2+rectangleFour k x y 3 := by
  change k+(k+x+y)=(k+x)+(k+y)
  abel

theorem fiberFour_translation (k v : E) (b : FiberParameters) :
    fiberFour (k-v) b=fun l=>fiberFour k b l-v := by
  ext l j
  fin_cases l <;> simp [fiberFour,planeShell,rectangleFour] <;> ring

theorem fiberFour_momentum (k : E) (b : FiberParameters) :
    fiberFour k b 0+fiberFour k b 1=fiberFour k b 2+fiberFour k b 3 := by
  exact rectangleFour_momentum _ _ _

def oppositeCorner (R ρ : ℝ) : Set FourMomenta := {q | q 1∈upperCorner R ρ}

theorem oppositeCorner_measurable (R ρ : ℝ) : MeasurableSet (oppositeCorner R ρ) :=
  (upperCorner_measurable R ρ).preimage (measurable_pi_apply 1)

theorem actual_opposite_corner_mass {R ρ : ℝ} (hρ : 0≤ρ) (k : E)
    (hk : k∈upperCorner R ρ) :
    fiberMeasure R k (oppositeCorner R ρ)≤
      ENNReal.ofReal (geometricFrequency ρ (k-boxCenter R ρ)) := by
  rw [geometricFrequency_eq_mass,ENNReal.ofReal_toReal (geometricFrequency_mass_finite hρ _).ne]
  rw [fiberMeasure_apply R k (oppositeCorner_measurable R ρ),
    fiberMeasure_apply ρ (k-boxCenter R ρ) MeasurableSet.univ]
  apply mul_le_mul_right _ (1/2:ℝ≥0∞)
  apply measure_mono
  intro b hb
  refine ⟨mem_univ _,?_⟩
  have hsmall := actual_momentum_small_box hρ (fiberFour k b) hk hb.1 hb.2
    (fiberFour_momentum k b)
  rw [fiberFour_translation]
  exact hsmall

end
end Resonance.OppositeCornerBox
