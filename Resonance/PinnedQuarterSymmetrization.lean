import Resonance.PinnedCoareaCurrentSymmetry
import Resonance.PinnedMollifierRoots

/-! Exact 1/4 symmetrization for the original common current, with genuine
absolute integrability of every complete-difference leg reading. -/
open Set MeasureTheory
open scoped ContDiff
namespace Resonance.PinnedQuarterSymmetrization
noncomputable section
open PinnedMeasure PinnedPeriodicity PinnedMeasureNormalization PinnedLegACCircle
open PinnedMaximalDifference PinnedSmoothDomain PinnedCircleMollifier PinnedTorusPermutations
open PinnedCoareaCurrentSymmetry BoxShrinkingKernel
local instance periodPositive : Fact (0<period) := ⟨period_pos⟩

def legSource (a : FourCircle→ℝ) (φ ψ : PinnedPeriodicity.Circle→ℂ)
    (i : Fin 4) (k : CircleMomenta) : ℂ :=
  ((a (fullLegs k):ℂ)*star (ψ (circleLeg i k)))*difference φ k

def legCurrent (d : ℝ) (a : FourCircle→ℝ) (φ ψ : PinnedPeriodicity.Circle→ℂ)
    (i : Fin 4) : ℂ := ∫k,legSource a φ ψ i k ∂euclideanCircleRegularCoarea d

theorem leg_weight_continuous {a : FourCircle→ℝ} (ha : Continuous a)
    {ψ : PinnedPeriodicity.Circle→ℂ} (hψ : Continuous ψ) (i : Fin 4) :
    Continuous (fun k=>(a (fullLegs k):ℂ)*star (ψ (circleLeg i k))) :=
  (Complex.continuous_ofReal.comp (ha.comp PinnedMollifierRoots.fullLegs_continuous)).mul
    (hψ.comp (circleLeg_continuous i)).star

theorem legSource_integrable {d : ℝ} (hd0 : 0<d) (hdU : d<1/2)
    {a : FourCircle→ℝ} (ha : Continuous a)
    {φ ψ : PinnedPeriodicity.Circle→ℂ} (hφ : Continuous φ)
    (hφ2 : ContDiff ℝ 2 (periodicLift φ)) (hψ : Continuous ψ) (i : Fin 4) :
    Integrable (legSource a φ ψ i) (euclideanCircleRegularCoarea d) :=
  (complete_source_limit hd0 hdU hφ hφ2 (leg_weight_continuous ha hψ i) kernel
    (fun η _=>kernel_measurable η) (fun η _=>kernel_integrable η)
    (fun _ hη=>kernel_nonneg hη) (fun _ hη=>kernel_mass hη)
    (fun _ _ _ hq=>kernel_support hq)).2.1

theorem legCurrent_transform {d : ℝ} (hd0 : 0<d) (hdU : d<1/2)
    {a : FourCircle→ℝ} (ha : Continuous a) (hasym : SymmetricWeight a)
    {φ ψ : PinnedPeriodicity.Circle→ℂ} (hφ : Continuous φ)
    (hφ2 : ContDiff ℝ 2 (periodicLift φ)) (hψ : Continuous ψ) (j : Fin 3) (i : Fin 4) :
    legCurrent d a φ ψ i=(sign j:ℂ)*legCurrent d a φ ψ (legIndex j i) := by
  have he := current_transform hd0 hdU hφ hφ2 (leg_weight_continuous ha hψ i) j
  simpa only [legCurrent,legSource,symmetric_weight_transform hasym,leg_transform] using he

theorem quarter_identity {d : ℝ} (hd0 : 0<d) (hdU : d<1/2)
    {a : FourCircle→ℝ} (ha : Continuous a) (hasym : SymmetricWeight a)
    {φ ψ : PinnedPeriodicity.Circle→ℂ} (hφ : Continuous φ)
    (hφ2 : ContDiff ℝ 2 (periodicLift φ)) (hψ : Continuous ψ) :
    (∫k,(a (fullLegs k):ℂ)*difference φ k*star (difference ψ k)
      ∂euclideanCircleRegularCoarea d)=4*legCurrent d a φ ψ 0 := by
  have hI := legCurrent_transform hd0 hdU ha hasym hφ hφ2 hψ 0 0
  have hP := legCurrent_transform hd0 hdU ha hasym hφ hφ2 hψ 2 0
  have hO := legCurrent_transform hd0 hdU ha hasym hφ hφ2 hψ 1 2
  change legCurrent d a φ ψ 0=(1:ℂ)*legCurrent d a φ ψ 1 at hI
  change legCurrent d a φ ψ 0=((-1:ℝ):ℂ)*legCurrent d a φ ψ 2 at hP
  change legCurrent d a φ ψ 2=(1:ℂ)*legCurrent d a φ ψ 3 at hO
  simp only [one_mul,Complex.ofReal_neg,Complex.ofReal_one,neg_one_mul] at hI hP hO
  have hi := legSource_integrable hd0 hdU ha hφ hφ2 hψ
  have he : (fun k=>(a (fullLegs k):ℂ)*difference φ k*star (difference ψ k))=
      fun k=>legSource a φ ψ 0 k+legSource a φ ψ 1 k-
        legSource a φ ψ 2 k-legSource a φ ψ 3 k := by
    funext k
    simp only [difference,star_sub,star_add,legSource]
    ring
  rw [he]
  have hsum := (integral_sub ((hi 0).add (hi 1) |>.sub (hi 2)) (hi 3)).trans
    (congrArg (fun z:ℂ=>z-legCurrent d a φ ψ 3)
      ((integral_sub ((hi 0).add (hi 1)) (hi 2)).trans
        (congrArg (fun z:ℂ=>z-legCurrent d a φ ψ 2) (integral_add (hi 0) (hi 1)))))
  apply hsum.trans
  change legCurrent d a φ ψ 0+legCurrent d a φ ψ 1-
    legCurrent d a φ ψ 2-legCurrent d a φ ψ 3=4*legCurrent d a φ ψ 0
  rw [←hI,←hO]
  linear_combination -2*hP

theorem gamma_quarter_identity {d : ℝ} (hd0 : 0<d) (hdU : d<1/2)
    {a : FourCircle→ℝ} (ha : Continuous a) (hasym : SymmetricWeight a)
    {φ ψ : PinnedPeriodicity.Circle→ℂ} (hφ : Continuous φ)
    (hφ2 : ContDiff ℝ 2 (periodicLift φ)) (hψ : Continuous ψ) (γ : ℝ) :
    (γ/4:ℂ)*(∫k,(a (fullLegs k):ℂ)*difference φ k*star (difference ψ k)
      ∂euclideanCircleRegularCoarea d)=(γ:ℂ)*legCurrent d a φ ψ 0 := by
  rw [quarter_identity hd0 hdU ha hasym hφ hφ2 hψ]
  ring

end
end Resonance.PinnedQuarterSymmetrization
