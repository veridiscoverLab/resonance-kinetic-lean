import Resonance.PinnedCircleMollifier
import Resonance.PinnedWeakOutputL1

/-! The two original tested regularization roots. All four entries of the
continuous weight remain in the common source. No finite-eta symmetry or
evenness of the kernel is used for the single-output root. -/
open Set MeasureTheory Filter
open scoped ContDiff Topology
namespace Resonance.PinnedMollifierRoots
noncomputable section
open PinnedMeasure PinnedPeriodicity PinnedMeasureNormalization PinnedClassificationFinal
open PinnedLegACCircle PinnedMaximalDifference PinnedSmoothDomain PinnedCircleMollifier
local instance periodPositive : Fact (0<period) := ⟨period_pos⟩

theorem fullLegs_continuous : Continuous fullLegs :=
  continuous_pi (fun i=>circleLeg_continuous i)

theorem original_mollified_form {d : ℝ} (hd0 : 0<d) (hdU : d<1/2)
    {a : FourCircle→ℝ} (ha : Continuous a)
    {φ ψ : PinnedPeriodicity.Circle→ℂ} (hφ : Continuous φ)
    (hφ2 : ContDiff ℝ 2 (periodicLift φ)) (hψ : Continuous ψ)
    (ρ : ℝ→ℝ→ℝ) (hρsmooth : ∀η,0<η → ContDiff ℝ ∞ (ρ η))
    (hρcompact : ∀η,0<η→HasCompactSupport (ρ η))
    (hpos : ∀η,0<η→∀q,0≤ρ η q) (hmass : ∀η,0<η→∫q,ρ η q=1)
    (hs : ∀η,0<η→∀q,ρ η q≠0→|q|≤η) :
    Tendsto (fun η=>∫k,ρ η (energy d k) •
      ((a (fullLegs k):ℂ)*difference φ k*star (difference ψ k))
      ∂Measure.pi (fun _:Fin 3=>circleHaar)) (𝓝[>]0)
      (𝓝 (∫k,(a (fullLegs k):ℂ)*difference φ k*star (difference ψ k)
        ∂euclideanCircleRegularCoarea d)) := by
  have hW : Continuous (fun k=>(a (fullLegs k):ℂ)*star (difference ψ k)) :=
    (Complex.continuous_ofReal.comp (ha.comp fullLegs_continuous)).mul
      (difference_continuous hψ).star
  have h := (complete_source_limit hd0 hdU hφ hφ2 hW ρ
    (fun η hη=>(hρsmooth η hη).continuous.measurable)
    (fun η hη=>(hρsmooth η hη).continuous.integrable_of_hasCompactSupport (hρcompact η hη))
    hpos hmass hs).2.2
  simpa only [mul_assoc,mul_left_comm,mul_comm] using h

theorem original_weak_mollifier {d : ℝ} (hd0 : 0<d) (hdU : d<1/2)
    {a : FourCircle→ℝ} (ha : Continuous a)
    {φ ψ : PinnedPeriodicity.Circle→ℂ} (hφ : Continuous φ)
    (hφ2 : ContDiff ℝ 2 (periodicLift φ)) (hψ : Continuous ψ) (γ : ℝ) (i : Fin 4)
    (ρ : ℝ→ℝ→ℝ) (hρsmooth : ∀η,0<η → ContDiff ℝ ∞ (ρ η))
    (hρcompact : ∀η,0<η→HasCompactSupport (ρ η))
    (hpos : ∀η,0<η→∀q,0≤ρ η q) (hmass : ∀η,0<η→∫q,ρ η q=1)
    (hs : ∀η,0<η→∀q,ρ η q≠0→|q|≤η) :
    Tendsto (fun η=>(γ:ℂ)*(∫k,ρ η (energy d k) •
      ((a (fullLegs k):ℂ)*difference φ k*star (ψ (circleLeg i k)))
      ∂Measure.pi (fun _:Fin 3=>circleHaar))) (𝓝[>]0)
      (𝓝 ((γ:ℂ)*(∫k,(a (fullLegs k):ℂ)*difference φ k*star (ψ (circleLeg i k))
        ∂euclideanCircleRegularCoarea d))) := by
  have hW : Continuous (fun k=>(a (fullLegs k):ℂ)*star (ψ (circleLeg i k))) :=
    (Complex.continuous_ofReal.comp (ha.comp fullLegs_continuous)).mul
      (hψ.comp (circleLeg_continuous i)).star
  have h := (complete_source_limit hd0 hdU hφ hφ2 hW ρ
    (fun η hη=>(hρsmooth η hη).continuous.measurable)
    (fun η hη=>(hρsmooth η hη).continuous.integrable_of_hasCompactSupport (hρcompact η hη))
    hpos hmass hs).2.2
  simpa only [mul_assoc,mul_left_comm,mul_comm] using
    (tendsto_const_nhds (x:=(γ:ℂ))).mul h

end
end Resonance.PinnedMollifierRoots
