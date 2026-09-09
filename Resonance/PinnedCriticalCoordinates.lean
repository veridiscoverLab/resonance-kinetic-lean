import Resonance.CoordinateReplacement
import Resonance.PinnedCriticalCancellation

/-! The two critical changes of variables are constructed from the original
shared factor. Their local invertibility is a consequence of the actual
dispersion and its previously proved critical classification. -/
open Real Set Filter
open scoped Topology ContDiff
namespace Resonance.PinnedCriticalCoordinates
noncomputable section
open PinnedGeometry PinnedMeasure PinnedCriticalFactor PinnedCriticalNormalization
open PinnedCriticalCancellation PinnedLocalArea CoordinateReplacement

def qCoordinates (d : ℝ) : Ambient → Ambient := replace 0 (sharedFactor d)

def vCoordinates (d : ℝ) : Ambient → Ambient := replace 2 (fun p => p 2*sharedFactor d p)

theorem qCoordinates_energy {d : ℝ} (hd0 : 0<d) (hdU : d<1/2) (p : Ambient) :
    rectangleEnergy d p = -(qCoordinates d p) 1*(qCoordinates d p) 2*(qCoordinates d p) 0 := by
  simpa [qCoordinates, replace_apply, show (2:Fin 3)≠0 by decide] using
    rectangleEnergy_factor hd0 hdU p

theorem vCoordinates_energy {d : ℝ} (hd0 : 0<d) (hdU : d<1/2) (p : Ambient) :
    rectangleEnergy d p = -(vCoordinates d p) 1*(vCoordinates d p) 2 := by
  simpa [vCoordinates, replace_apply, show (1:Fin 3)≠2 by decide, mul_assoc] using
    rectangleEnergy_factor hd0 hdU p

theorem vCoordinates_difference {φ : ℝ→ℂ} (hφ : ContDiff ℝ 2 φ)
    {d : ℝ} {p : Ambient} (hG : sharedFactor d p≠0) :
    fullDifference φ (rectangleMap p) =
      ((-(vCoordinates d p) 1*(vCoordinates d p) 2 : ℝ) : ℂ)*
        (complexFactor φ p / (sharedFactor d p : ℂ)) := by
  rw [complex_rectangle_factor hφ]
  simp only [vCoordinates, replace_apply]
  norm_num
  have hGc : (sharedFactor d p : ℂ)≠0 := Complex.ofReal_ne_zero.mpr hG
  push_cast
  field_simp

theorem qCoordinates_local_inverse {d z u v : ℝ} (hd0 : 0<d) (hdU : d<1/2)
    (hn : deriv (fun t : ℝ => sharedFactor d (WithLp.toLp 2 ![t,u,v])) z≠0) :
    ∃ e : OpenPartialHomeomorph Ambient Ambient,
      (e : Ambient → Ambient)=qCoordinates d ∧
      WithLp.toLp 2 ![z,u,v]∈e.source ∧
      ContDiffAt ℝ 1 e.symm (e (WithLp.toLp 2 ![z,u,v])) := by
  let p : Ambient := WithLp.toLp 2 ![z,u,v]
  have hc := (sharedFactor_contDiff_one hd0 hdU).contDiffAt (x:=p)
  have hd := (hc.differentiableAt (by norm_num)).hasFDerivAt.comp_hasDerivAt z
    (parameter_z_hasDerivAt z u v)
  change HasDerivAt (fun t : ℝ => sharedFactor d (WithLp.toLp 2 ![t,u,v]))
    ((fderiv ℝ (sharedFactor d) p) (WithLp.toLp 2 ![1,0,0])) z at hd
  have he : deriv (fun t : ℝ => sharedFactor d (WithLp.toLp 2 ![t,u,v])) z =
      (fderiv ℝ (sharedFactor d) p) (unit 0) := by
    rw [hd.deriv]
    congr 1
    ext i
    fin_cases i <;> simp [CoordinateReplacement.unit]
  rw [he] at hn
  exact local_coordinate_exists hc 0 hn

theorem vCoordinates_local_inverse {d : ℝ} (hd0 : 0<d) (hdU : d<1/2)
    {p : Ambient} (hv : p 2=0) (hG : sharedFactor d p≠0) :
    ∃ e : OpenPartialHomeomorph Ambient Ambient,
      (e : Ambient → Ambient)=vCoordinates d ∧ p∈e.source ∧
      ContDiffAt ℝ 1 e.symm (e p) := by
  have hGc := (sharedFactor_contDiff_one hd0 hdU).contDiffAt (x:=p)
  have hFc : ContDiffAt ℝ 1 (fun q : Ambient => q 2*sharedFactor d q) p :=
    (coordinateProjection 2).contDiff.contDiffAt.mul hGc
  have hd := (coordinateProjection 2).hasFDerivAt.mul
    (hGc.differentiableAt (by norm_num)).hasFDerivAt
  change HasFDerivAt (fun q : Ambient => q 2*sharedFactor d q)
    (p 2 • fderiv ℝ (sharedFactor d) p + sharedFactor d p • coordinateProjection 2) p at hd
  have hn : (fderiv ℝ (fun q : Ambient => q 2*sharedFactor d q) p) (unit 2)≠0 := by
    rw [hd.fderiv]
    simpa [hv, coordinateProjection, CoordinateReplacement.unit] using hG
  exact local_coordinate_exists hFc 2 hn

theorem every_critical_point_coordinates {d : ℝ} (hd0 : 0<d) (hdU : d<1/2)
    {k : Ambient} (he : liftedEnergy d k=0) (hg : energyGradient d k=0) :
    ∃ swap : Bool, ∃ n m : ℤ, ∃ z v : ℝ,
      criticalGauge swap n m (WithLp.toLp 2 ![z,0,v])=k ∧
      ∃ e : OpenPartialHomeomorph Ambient Ambient,
        WithLp.toLp 2 ![z,0,v]∈e.source ∧
        ContDiffAt ℝ 1 e.symm (e (WithLp.toLp 2 ![z,0,v])) ∧
        ((v=0 ∧ sharedFactor d (WithLp.toLp 2 ![z,0,v])≠0 ∧
          (e : Ambient → Ambient)=vCoordinates d) ∨
         (sharedFactor d (WithLp.toLp 2 ![z,0,v])=0 ∧
          (e : Ambient → Ambient)=qCoordinates d)) := by
  obtain ⟨swap,n,m,z,v,hk,hcase,hvel⟩ := every_critical_point_normalized hd0 hdU he hg
  refine ⟨swap,n,m,z,v,hk,?_⟩
  by_cases hG : sharedFactor d (WithLp.toLp 2 ![z,0,v])=0
  · have hn : deriv (fun t : ℝ => sharedFactor d (WithLp.toLp 2 ![t,0,v])) z≠0 := by
      rcases hcase with hv | hc
      · subst v
        exact (sharedFactor_origin_alternative hd0 hdU z).resolve_left (not_not.mpr hG)
      · exact (sharedFactor_separated_noncritical hd0 hdU hvel hc).2
    obtain ⟨e,heq,hsource,hinv⟩ := qCoordinates_local_inverse hd0 hdU hn
    exact ⟨e,hsource,hinv,Or.inr ⟨hG,heq⟩⟩
  · have hv0 : v=0 := by
      have hvG := sharedFactor_separated hd0 hdU z v
      rw [hvel,sub_self] at hvG
      exact (mul_eq_zero.mp hvG).resolve_right hG
    obtain ⟨e,heq,hsource,hinv⟩ := vCoordinates_local_inverse hd0 hdU
      (p:=WithLp.toLp 2 ![z,0,v]) (by simpa using hv0) hG
    exact ⟨e,hsource,hinv,Or.inl ⟨hv0,hG,heq⟩⟩

end
end Resonance.PinnedCriticalCoordinates
