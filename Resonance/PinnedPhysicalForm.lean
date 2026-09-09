import Resonance.PinnedPhysicalMultiplier
import Resonance.ClosedPullback

/-! The original pinned physical full-difference form, retaining its
actual quartet weight and maximal domain under g -> g/N. -/
open MeasureTheory Set LinearPMap
open scoped ComplexConjugate
namespace Resonance.PinnedPhysicalForm
noncomputable section
open PinnedPeriodicity PinnedEndToEnd PinnedClassificationFinal
open PinnedMaximalDifference PinnedSmoothDomain PinnedClosedForm PinnedScaledDifference
open PinnedPhysicalMultiplier
local notation "Circle" => PinnedPeriodicity.Circle
local instance periodPositive : Fact (0 < period) := ⟨period_pos⟩

def physicalDifference {d : ℝ} (hd0 : 0 < d) (hdU : d < 1/2)
    (N : C(Circle,ℝ)) (hN : ∀x,0 < N x) : Source→ₗ.[ℂ]Target d (physicalWeight d N) :=
  ClosedPullback.pullback (maximalDifference hd0 hdU (physicalWeight d N))
    (physicalEquivalence N hN)

abbrev PhysicalDomain {d : ℝ} (hd0 : 0 < d) (hdU : d < 1/2)
    (N : C(Circle,ℝ)) (hN : ∀x,0 < N x) := (physicalDifference hd0 hdU N hN).domain

def physicalForm {d : ℝ} (hd0 : 0 < d) (hdU : d < 1/2)
    (N : C(Circle,ℝ)) (hN : ∀x,0 < N x) (γ : ℝ)
    (u v : PhysicalDomain hd0 hdU N hN) : ℂ :=
  (γ/4 : ℂ)*inner ℂ (physicalDifference hd0 hdU N hN v) (physicalDifference hd0 hdU N hN u)

theorem physicalDifference_closed {d : ℝ} (hd0 : 0 < d) (hdU : d < 1/2)
    (N : C(Circle,ℝ)) (hN : ∀x,0 < N x) : (physicalDifference hd0 hdU N hN).IsClosed :=
  ClosedPullback.pullback_closed _ (maximalDifference_isClosed hd0 hdU _) _

theorem physicalDifference_dense {d : ℝ} (hd0 : 0 < d) (hdU : d < 1/2)
    (N : C(Circle,ℝ)) (hN : ∀x,0 < N x) :
    Dense (PhysicalDomain hd0 hdU N hN : Set Source) :=
  ClosedPullback.pullback_dense _ (maximalDifference_dense_domain hd0 hdU
    (physicalWeight_continuous hd0 hdU N)) _

theorem physical_domain_iff {d : ℝ} (hd0 : 0 < d) (hdU : d < 1/2)
    (N : C(Circle,ℝ)) (hN : ∀x,0 < N x) (u : Source) :
    u∈PhysicalDomain hd0 hdU N hN ↔
      MemLp (difference (fun x=>u x/(N x : ℂ))) 2 (weightedCoarea d (physicalWeight d N)) := by
  rw [PhysicalDomain,physicalDifference,ClosedPullback.domain_iff,maximalDifference_domain_iff]
  exact memLp_congr_ae (difference_ae_congr hd0 hdU _ (physicalEquivalence_ae N hN u))

theorem physicalForm_integral {d : ℝ} (hd0 : 0 < d) (hdU : d < 1/2)
    (N : C(Circle,ℝ)) (hN : ∀x,0 < N x) (γ : ℝ)
    (u v : PhysicalDomain hd0 hdU N hN) :
    physicalForm hd0 hdU N hN γ u v=(γ/4 : ℂ)*
      ∫k,difference (fun x=>(u : Source) x/(N x : ℂ)) k*
        conj (difference (fun x=>(v : Source) x/(N x : ℂ)) k)
        ∂weightedCoarea d (physicalWeight d N) := by
  let T := maximalDifference hd0 hdU (physicalWeight d N)
  let U := physicalEquivalence N hN
  change PinnedOperator.paperForm hd0 hdU (physicalWeight d N) γ
    (ClosedPullback.domainMap T U u) (ClosedPullback.domainMap T U v)= _
  rw [PinnedOperator.paperForm_integral]
  congr 1
  apply integral_congr_ae
  filter_upwards [difference_ae_congr hd0 hdU (physicalWeight d N)
    (physicalEquivalence_ae N hN (u : Source)),
    difference_ae_congr hd0 hdU (physicalWeight d N)
      (physicalEquivalence_ae N hN (v : Source))] with k hu hv
  change difference (U (u : Source)) k*conj (difference (U (v : Source)) k)= _
  rw [hu,hv]

theorem physical_kernel_classification {d : ℝ} (hd0 : 0 < d) (hdU : d < 1/2)
    (N : C(Circle,ℝ)) (hN : ∀x,0 < N x) (u : Source) :
    (u,0)∈(physicalDifference hd0 hdU N hN).graph ↔
      ExistsUnique (fun AB : ℂ × ℂ => (u : Circle→ℂ)=ᵐ[circleHaar]
        (fun x=>(N x : ℂ)*(AB.1+AB.2*(circleDispersion d x : ℂ)))) := by
  rw [physicalDifference,ClosedPullback.graph_iff,maximalDifference_graph]
  change (physicalEquivalence N hN u,0)∈maximalGraph d (physicalWeight d N) ↔ _
  rw [maximalGraph_kernel_classification hd0 hdU _
    (physicalWeight_continuous hd0 hdU N) (physicalWeight_positive hd0 hdU N hN)]
  apply existsUnique_congr
  intro AB
  constructor
  · intro ha
    filter_upwards [ha,physicalEquivalence_ae N hN u] with x hx hu
    rw [hu] at hx
    exact (div_eq_iff (Complex.ofReal_ne_zero.mpr (hN x).ne')).mp hx |>.trans (mul_comm _ _)
  · intro ha
    filter_upwards [ha,physicalEquivalence_ae N hN u] with x hx hu
    rw [hu,hx,mul_div_cancel_left₀ _ (Complex.ofReal_ne_zero.mpr (hN x).ne')]

def physicalOperator {d : ℝ} (hd0 : 0 < d) (hdU : d < 1/2)
    (N : C(Circle,ℝ)) (hN : ∀x,0 < N x) (γ : ℝ) : Source→ₗ.[ℂ]Source :=
  ClosedOperatorRepresentation.square (ClosedPullback.pullback
    (scaledDifference hd0 hdU (physicalWeight d N) γ) (physicalEquivalence N hN))

theorem physicalOperator_selfAdjoint {d : ℝ} (hd0 : 0 < d) (hdU : d < 1/2)
    (N : C(Circle,ℝ)) (hN : ∀x,0 < N x) {γ : ℝ} (hγ : 0 < γ) :
    IsSelfAdjoint (physicalOperator hd0 hdU N hN γ) :=
  ClosedPullback.pullback_square_selfAdjoint _ (scaledDifference_isClosed hd0 hdU _ hγ)
    (scaledDifference_dense_domain hd0 hdU (physicalWeight_continuous hd0 hdU N) γ) _

end
end Resonance.PinnedPhysicalForm
