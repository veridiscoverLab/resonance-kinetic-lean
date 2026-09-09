import Resonance.PinnedAverageBounds
import Mathlib.Topology.ContinuousMap.Bounded.ArzelaAscoli
import Mathlib.Topology.MetricSpace.Equicontinuity
import Mathlib.Topology.Sequences

/-! Local compactness is proved from uniform value and derivative bounds,
via the genuine Arzela--Ascoli theorem.  The subsequent actual-average
interface obtains these bounds from source integration by parts. -/
open Real MeasureTheory Set Filter
open scoped ENNReal NNReal Topology ContDiff BoundedContinuousFunction
namespace Resonance.PinnedAverageCompactness
noncomputable section

theorem bounded_C1_subsequence {a b : ℝ} {F : ℕ → ℝ → ℂ} (B₀ B₁ : ℝ≥0)
    (hF : ∀ n x, x∈Icc a b → DifferentiableAt ℝ (F n) x)
    (hb₀ : ∀ n x, x∈Icc a b → ‖F n x‖₊ ≤ B₀)
    (hb₁ : ∀ n x, x∈Icc a b → ‖deriv (F n) x‖₊ ≤ B₁) :
    ∃ g : (Icc a b) →ᵇ ℂ, ∃ s : ℕ → ℕ, StrictMono s ∧
      TendstoUniformly (fun n (x : Icc a b) => F (s n) x) g atTop := by
  let A : ℕ → (Icc a b) →ᵇ ℂ := fun n => BoundedContinuousFunction.mkOfCompact
    ⟨fun x => F n x,
      continuousOn_iff_continuous_restrict.mp
        (fun x hx => (hF n x hx).continuousAt.continuousWithinAt)⟩
  have hLip (n : ℕ) : LipschitzWith B₁ (A n) := by
    have hh := (convex_Icc a b).lipschitzOnWith_of_nnnorm_deriv_le
      (fun x hx => hF n x hx) (fun x hx => hb₁ n x hx)
    intro x y
    exact hh x.2 y.2
  have hequi : Equicontinuous ((↑) : (range A) → (Icc a b) → ℂ) := by
    apply Metric.equicontinuous_of_continuity_modulus (fun r => (B₁:ℝ)*r)
      (by simpa using (continuous_const.mul continuous_id :
        Continuous (fun r : ℝ => (B₁:ℝ)*r)).tendsto 0)
    intro x y f
    obtain ⟨n,hn⟩ := f.2
    simpa [← hn] using (hLip n).dist_le_mul x y
  have hcompact : IsCompact (closure (range A)) :=
    BoundedContinuousFunction.arzela_ascoli (Metric.closedBall (0:ℂ) B₀)
      (isCompact_closedBall (0:ℂ) B₀) (range A)
      (by
        intro f x hf
        obtain ⟨n,rfl⟩ := hf
        simpa [Metric.mem_closedBall, dist_zero_right, A] using hb₀ n x x.2)
      hequi
  obtain ⟨g,_hg,s,hs,hconv⟩ := hcompact.tendsto_subseq
    (fun n => subset_closure (mem_range_self n))
  exact ⟨g,s,hs,BoundedContinuousFunction.tendsto_iff_tendstoUniformly.mp hconv⟩

/-- Actual source averages of a uniformly L¹-bounded family are locally
precompact.  Neither compactness nor a derivative estimate is an input:
both are derived from the original source-map Jacobian and same-graph IBP. -/
theorem actual_average_subsequence
    {I I₀ J K : Set ℝ}
    (hI : IsOpen I) (hI₀ : IsOpen I₀) (hJ : IsOpen J)
    (hK : IsCompact K) (hIK : I ⊆ K) (hKI : K ⊆ I₀)
    {a b l r : ℝ} (hab : a ≤ b) (hsub : Icc a b ⊆ J) (hlr : Icc l r ⊆ I)
    {H χ : ℝ × ℝ → ℝ}
    (hH : ContDiffOn ℝ ∞ H (I₀ ×ˢ J))
    (hχ : ContDiffOn ℝ ∞ χ (I₀ ×ˢ J))
    (hZ : ∀ p ∈ I₀ ×ˢ J, PinnedSmoothing.partialZ H p ≠ 0)
    (hχedge : ∀ x∈I₀, χ (x,a)=0 ∧ χ (x,b)=0)
    {ν : Measure ℝ} [IsFiniteMeasureOnCompacts ν]
    {C R : ℝ≥0∞} (hC : C ≠ ⊤) (hR : R ≠ ⊤)
    (hmap : ∀ x∈I, AEMeasurable (fun z => H (x,z)) (volume.restrict (Icc a b)))
    (hdom : ∀ x∈I, (volume.restrict (Icc a b)).map (fun z => H (x,z)) ≤ C • ν)
    {f : ℕ → ℝ → ℂ} (hf : ∀ n, Integrable (f n) ν)
    (hbound : ∀ n, eLpNorm (f n) 1 ν ≤ R) :
    ∃ g : (Icc l r) →ᵇ ℂ, ∃ s : ℕ → ℕ, StrictMono s ∧
      TendstoUniformly
        (fun n (x : Icc l r) => ∫ z in Icc a b, χ (x,z) • f (s n) (H (x,z))) g atTop := by
  obtain ⟨C₀,C₁,hC₀,hC₁,hall⟩ := PinnedAverageBounds.actual_L1_average_uniform_C1
    hI hI₀ hJ hK hIK hKI hab hsub hH hχ hZ hχedge hC hmap hdom
  let A : ℕ → ℝ → ℂ := fun n x => ∫ z in Icc a b, χ (x,z) • f n (H (x,z))
  have hD (n : ℕ) (x : ℝ) (hx : x∈Icc l r) := hall (f n) (hf n) x (hlr hx)
  apply bounded_C1_subsequence (F:=A) (C₀*R).toNNReal (C₁*R).toNNReal
  · intro n x hx
    exact (hD n x hx).1.differentiableAt
  · intro n x hx
    apply ENNReal.le_toNNReal_of_coe_le _ (ENNReal.mul_ne_top hC₀ hR)
    exact ((hD n x hx).2.1).trans (mul_le_mul_right (hbound n) C₀)
  · intro n x hx
    apply ENNReal.le_toNNReal_of_coe_le _ (ENNReal.mul_ne_top hC₁ hR)
    exact ((hD n x hx).2.2).trans (mul_le_mul_right (hbound n) C₁)

end
end Resonance.PinnedAverageCompactness
