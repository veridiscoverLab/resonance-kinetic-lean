import Resonance.PinnedCriticalQAmplitude
import Resonance.PinnedCompleteSourceCutoff
import Resonance.PinnedCompactRegular

/-! The actual q=G chart becomes regular after cutting off its shared uv.
This uses the original energy gradient, not a replacement surface measure. -/
open Set MeasureTheory
open scoped ContDiff InnerProductSpace
namespace Resonance.PinnedCriticalQCutoff
noncomputable section
open PinnedMeasure PinnedPeriodicity PinnedCriticalFactor PinnedCriticalCancellation
open PinnedCriticalGauge PinnedCompleteSourceCutoff PinnedCriticalQAmplitude
open CoordinateReplacement PinnedCriticalCoordinates

def sourceCutoff (W : Ambient → ℂ) (swap : Bool) (n m : ℤ) (δ : ℝ) (k : Ambient) : ℂ :=
  CriticalSourceCutoff.cutoff δ (sharedProduct swap n m k) • W k

theorem sourceCutoff_regular {W : Ambient → ℂ} (hW : Continuous W)
    (hK : HasCompactSupport W) (swap : Bool) (n m : ℤ) (δ : ℝ) :
    Continuous (sourceCutoff W swap n m δ) ∧ HasCompactSupport (sourceCutoff W swap n m δ) := by
  constructor
  · unfold sourceCutoff
    simp only [Complex.real_smul]
    exact (Complex.continuous_ofReal.comp ((CriticalSourceCutoff.cutoff_continuous δ).comp
      (sharedProduct_continuous swap n m))).mul hW
  · apply HasCompactSupport.of_support_subset_isCompact hK
    intro k hk
    apply subset_tsupport
    intro hz
    exact hk (by simp [sourceCutoff,hz])

theorem sourceCutoff_support (W : Ambient → ℂ) (swap : Bool) (n m : ℤ) (δ : ℝ) :
    tsupport (sourceCutoff W swap n m δ)⊆tsupport W := tsupport_smul_subset_right _ _

theorem sourceCutoff_pullback (W : Ambient → ℂ) (swap : Bool) (n m : ℤ) (δ : ℝ)
    (p : Ambient) : sourceCutoff W swap n m δ (gaugeHomeomorph swap n m p)=
      CriticalSourceCutoff.cutoff δ (p 1*p 2) • W (gaugeHomeomorph swap n m p) := by
  simp [sourceCutoff,sharedProduct]

theorem sourceCutoff_support_chart (W : Ambient → ℂ) (swap : Bool) (n m : ℤ) (δ : ℝ)
    {S : Set Ambient} (hS : tsupport (W ∘ gaugeHomeomorph swap n m)⊆S) :
    tsupport (sourceCutoff W swap n m δ ∘ gaugeHomeomorph swap n m)⊆S := by
  rw [tsupport_comp_eq_preimage] at hS ⊢
  exact (preimage_mono (sourceCutoff_support W swap n m δ)).trans hS

theorem sourceCutoff_amplitude {d : ℝ} (φ : ℝ → ℂ) (W : Ambient → ℂ)
    (swap : Bool) (n m : ℤ) (e : OpenPartialHomeomorph Ambient Ambient)
    (he : (e : Ambient → Ambient)=qCoordinates d) (δ : ℝ) :
    amplitude d φ (sourceCutoff W swap n m δ) swap n m e=
      fun q=>CriticalSourceCutoff.cutoff δ (q 1*q 2) • amplitude d φ W swap n m e q := by
  have hc : coefficient φ (sourceCutoff W swap n m δ) swap n m=
      fun p=>CriticalSourceCutoff.cutoff δ (p 1*p 2) • coefficient φ W swap n m p := by
    funext p
    simp only [coefficient,sourceCutoff_pullback,Complex.real_smul]
    ring
  unfold amplitude
  rw [hc]
  apply CoordinateFactoredAmplitude.factored_formula
  intro p _
  rw [he]
  simp [qCoordinates,replace_apply,show (1:Fin 3)≠0 by decide,show (2:Fin 3)≠0 by decide]

theorem partial_factorZ {d : ℝ} (hd0 : 0<d) (hdU : d<1/2) (p : Ambient) :
    (fderiv ℝ (sharedFactor d) p) (unit 0)=factorZDerivative d p := by
  have hp : WithLp.toLp 2 ![p 0,p 1,p 2]=p := by ext i; fin_cases i <;> rfl
  have hu : (WithLp.toLp 2 ![1,0,0] : Ambient)=unit 0 := by ext i; fin_cases i <;> simp [CoordinateReplacement.unit]
  have hd := ((sharedFactor_contDiff_one hd0 hdU).differentiable (by norm_num)
    (WithLp.toLp 2 ![p 0,p 1,p 2])).hasFDerivAt.comp_hasDerivAt
    (p 0) (parameter_z_hasDerivAt (p 0) (p 1) (p 2))
  have he := hd.unique (sharedFactor_z_hasDerivAt hd0 hdU (p 0) (p 1) (p 2))
  simpa only [hu,hp] using he

theorem cutoff_original_gradient {d : ℝ} (hd0 : 0<d) (hdU : d<1/2)
    (φ : ℝ → ℂ) (W : Ambient → ℂ) (swap : Bool) (n m : ℤ)
    (e : OpenPartialHomeomorph Ambient Ambient)
    (hn : ∀p∈e.source,(fderiv ℝ (sharedFactor d) p) (unit 0)≠0)
    (hS : tsupport (W ∘ gaugeHomeomorph swap n m)⊆e.source)
    {δ : ℝ} (hδ : 0<δ) :
    ∀k∈tsupport (fun k=>sourceCutoff W swap n m δ k*fullDifference φ k),energyGradient d k≠0 := by
  intro k hk hg
  have hkW := (sourceCutoff_support W swap n m δ) (tsupport_mul_subset_left hk)
  have hkχ : k∈tsupport (fun k=>CriticalSourceCutoff.cutoff δ (sharedProduct swap n m k)) := by
    have he : (fun k=>sourceCutoff W swap n m δ k*fullDifference φ k)=
        fun k=>CriticalSourceCutoff.cutoff δ (sharedProduct swap n m k) • (W k*fullDifference φ k) := by
      funext k
      exact smul_mul_assoc _ _ _
    rw [he] at hk
    exact (tsupport_smul_subset_left _ _) hk
  have hb : sharedProduct swap n m k≠0 := by
    have hx := CriticalSourceCutoff.cutoff_support (sharedProduct_continuous swap n m) hδ hkχ
    intro hz
    simp [hz] at hx
    exact (not_le_of_gt hδ) hx
  let p := (gaugeHomeomorph swap n m).symm k
  have hpk : gaugeHomeomorph swap n m p=k := (gaugeHomeomorph swap n m).apply_symm_apply k
  have hps : p∈e.source := by
    apply hS
    rw [tsupport_comp_eq_preimage]
    simpa only [mem_preimage,hpk] using hkW
  have hJ : factorZDerivative d p≠0 := by rw [←partial_factorZ hd0 hdU]; exact hn p hps
  have hd := energy_direction_factor hd0 hdU swap n m p
  rw [←gaugeHomeomorph_apply,hpk,hg] at hd
  have hz : -p 1*p 2*factorZDerivative d p=0 := by simpa using hd.symm
  have hb' : p 1*p 2≠0 := hb
  exact (mul_ne_zero (by simpa only [neg_mul] using neg_ne_zero.mpr hb') hJ) hz

end
end Resonance.PinnedCriticalQCutoff
