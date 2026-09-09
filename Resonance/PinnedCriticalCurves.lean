import Resonance.PinnedSurfaceNull

/-! The projection-critical set is controlled by the common original velocity,
not by a selection of resonance branches. -/
open Real MeasureTheory Set Filter
open scoped ENNReal NNReal Topology ContDiff
namespace Resonance.PinnedCriticalCurves
noncomputable section
open Resonance.PinnedGeometry Resonance.PinnedCharts Resonance.PinnedMeasure
open Resonance.PinnedSurfaceNull

theorem real_local_inverse {v : ℝ→ℝ} {z : ℝ}
    (hv : ContDiffAt ℝ 1 v z) (hz : deriv v z ≠ 0) :
    ∃ Z : ℝ→ℝ, Z (v z)=z ∧ ContDiffAt ℝ 1 Z (v z) ∧
      (∀ᶠ t in 𝓝 z, Z (v t)=t) := by
  let L := fderiv ℝ v z
  have hL (b : ℝ) : L b=deriv v z*b := by
    dsimp [L]
    rw [(hv.differentiableAt (by norm_num)).hasDerivAt.hasFDerivAt.fderiv]
    simp [mul_comm]
  have hinj : Function.Injective L := by
    intro a b hab
    rw [hL,hL] at hab
    exact mul_left_cancel₀ hz hab
  let e : ℝ ≃L[ℝ] ℝ :=
    (LinearEquiv.ofBijective L.toLinearMap
      ⟨hinj,LinearMap.injective_iff_surjective.mp hinj⟩).toContinuousLinearEquiv
  have hd : HasFDerivAt v (e : ℝ→L[ℝ]ℝ) z :=
    (hv.differentiableAt (by norm_num)).hasFDerivAt
  refine ⟨hv.localInverse hd (by norm_num),hv.localInverse_apply_image hd (by norm_num),
    hv.to_localInverse hd (by norm_num),?_⟩
  exact (hv.hasStrictFDerivAt' hd (by norm_num)).eventually_left_inverse

def commonVelocitySet (v : ℝ→ℝ) : Set Ambient :=
  {k | v (k 1)=v (k 2) ∧ v (k 1)=v (k 0+k 1-k 2)}

theorem common_velocity_locally_curve {v : ℝ→ℝ} (hv : ContDiff ℝ 1 v)
    {k : Ambient} (hk : k ∈ commonVelocitySet v)
    (hz : deriv v (k 2)≠0) (hw : deriv v (k 0+k 1-k 2)≠0) :
    ∃ V ∈ 𝓝[commonVelocitySet v] k, (μH[2] : Measure Ambient) V=0 := by
  obtain ⟨Z,hZ,hZc,hZinv⟩ := real_local_inverse hv.contDiffAt hz
  obtain ⟨W,hW,hWc,hWinv⟩ := real_local_inverse hv.contDiffAt hw
  let γ : ℝ→Ambient := fun t => WithLp.toLp 2 ![W (v t)-t+Z (v t),t,Z (v t)]
  have hZy : ContDiffAt ℝ 1 (fun t => Z (v t)) (k 1) := by
    exact (hk.1 ▸ hZc).comp (k 1) hv.contDiffAt
  have hWy : ContDiffAt ℝ 1 (fun t => W (v t)) (k 1) := by
    exact (hk.2 ▸ hWc).comp (k 1) hv.contDiffAt
  have hγ : ContDiffAt ℝ 1 γ (k 1) := by
    rw [contDiffAt_piLp]
    intro i
    fin_cases i
    · exact (hWy.sub contDiffAt_id).add hZy
    · exact contDiffAt_id
    · exact hZy
  obtain ⟨I,hI,hzero⟩ := smooth_curve_local_null hγ
  have hnear : ∀ᶠ p : Ambient in 𝓝 k,
      p 1∈I ∧ Z (v (p 2))=p 2 ∧ W (v (p 0+p 1-p 2))=p 0+p 1-p 2 := by
    have h1 := (coordinateProjection 1).continuous.continuousAt.tendsto.eventually hI
    have h2 := (coordinateProjection 2).continuous.continuousAt.tendsto.eventually hZinv
    have h3 := (coordinateProjection 0+coordinateProjection 1-coordinateProjection 2
      ).continuous.continuousAt.tendsto.eventually hWinv
    exact h1.and (h2.and h3)
  let V := {p : Ambient | p∈commonVelocitySet v ∧
      p 1∈I ∧ Z (v (p 2))=p 2 ∧ W (v (p 0+p 1-p 2))=p 0+p 1-p 2}
  refine ⟨V,inter_mem self_mem_nhdsWithin (mem_nhdsWithin_of_mem_nhds hnear),?_⟩
  apply measure_mono_null _ hzero
  rintro p ⟨hp,hpI,hpZ,hpW⟩
  refine ⟨p 1,hpI,?_⟩
  have heZ : Z (v (p 1))=p 2 := by rw [hp.1,hpZ]
  have heW : W (v (p 1))=p 0+p 1-p 2 := by rw [hp.2,hpW]
  ext i
  fin_cases i <;> simp [γ,heZ,heW]
  ring

theorem common_velocity_exceptional_countable {v : ℝ→ℝ}
    (hlevels : ∀ a : ℝ, Set.Countable {t | v t=a})
    (hcrit : Set.Countable {t | deriv v t=0}) :
    Set.Countable {k : Ambient | k∈commonVelocitySet v ∧
      (deriv v (k 2)=0 ∨ deriv v (k 0+k 1-k 2)=0)} := by
  let C : Set ℝ := v '' {t | deriv v t=0}
  let L (a : ℝ) : Set ℝ := {t | v t=a}
  let encode : ℝ×(ℝ×ℝ)→Ambient := fun p =>
    WithLp.toLp 2 ![p.2.2-p.1+p.2.1,p.1,p.2.1]
  have hC : C.Countable := hcrit.image v
  have hT : (⋃ a∈C, encode '' (L a ×ˢ (L a ×ˢ L a))).Countable := by
    apply hC.biUnion
    intro a _
    exact ((hlevels a).prod ((hlevels a).prod (hlevels a))).image encode
  apply hT.mono
  rintro k ⟨hk,hbad⟩
  have ha : v (k 1)∈C := by
    rcases hbad with hz | hw
    · exact ⟨k 2,hz,hk.1.symm⟩
    · exact ⟨k 0+k 1-k 2,hw,hk.2.symm⟩
  apply mem_iUnion_of_mem (v (k 1))
  apply mem_iUnion_of_mem ha
  refine ⟨(k 1,(k 2,k 0+k 1-k 2)),⟨rfl,hk.1.symm,hk.2.symm⟩,?_⟩
  ext i
  fin_cases i <;> simp [encode]
  ring

/-- The whole common-velocity locus is H²-null.  The statement is applied below
to the actual pinned velocity, whose level and critical sets are proved countable. -/
theorem common_velocity_hausdorff_null {v : ℝ→ℝ} (hv : ContDiff ℝ 1 v)
    (hlevels : ∀ a : ℝ, Set.Countable {t | v t=a})
    (hcrit : Set.Countable {t | deriv v t=0}) :
    (μH[2] : Measure Ambient) (commonVelocitySet v)=0 := by
  let B : Set Ambient := {k | k∈commonVelocitySet v ∧
    (deriv v (k 2)=0 ∨ deriv v (k 0+k 1-k 2)=0)}
  let G : Set Ambient := {k | k∈commonVelocitySet v ∧
    deriv v (k 2)≠0 ∧ deriv v (k 0+k 1-k 2)≠0}
  have hB : (μH[2] : Measure Ambient) B=0 := by
    letI := Measure.noAtoms_hausdorff Ambient (by norm_num : (0:ℝ)<2)
    exact (common_velocity_exceptional_countable hlevels hcrit).measure_zero _
  have hG : (μH[2] : Measure Ambient) G=0 := by
    apply measure_null_of_locally_null G
    intro k hk
    obtain ⟨V,hV,hzero⟩ := common_velocity_locally_curve hv hk.1 hk.2.1 hk.2.2
    refine ⟨V,?_,hzero⟩
    exact nhdsWithin_mono k (show G⊆commonVelocitySet v from fun _ h => h.1) hV
  apply measure_mono_null (t := G ∪ B) ?_ (measure_union_null hG hB)
  intro k hk
  by_cases hz : deriv v (k 2)=0
  · exact Or.inr ⟨hk,Or.inl hz⟩
  by_cases hw : deriv v (k 0+k 1-k 2)=0
  · exact Or.inr ⟨hk,Or.inr hw⟩
  exact Or.inl ⟨hk,hz,hw⟩

end
end Resonance.PinnedCriticalCurves
