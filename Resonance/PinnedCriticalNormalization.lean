import Resonance.PinnedLocalArea
import Resonance.PinnedPeriodicity
import Resonance.PinnedLegAC

/-! Complete periodic normalization of every critical quartet. The map is a
fixed affine change of the same three independent momenta, and the fourth leg
is still their signed sum. -/
open Real Set MeasureTheory
open scoped Topology ContDiff
namespace Resonance.PinnedCriticalNormalization
noncomputable section
open Resonance.PinnedGeometry Resonance.PinnedMeasure Resonance.PinnedPeriodicity
open Resonance.PinnedCriticalGeometry Resonance.PinnedCriticalFactor

def rectangleMap : Ambient→L[ℝ] Ambient :=
  ({ toFun := fun p => WithLp.toLp 2 ![p 0+p 1,p 0+p 2,p 0]
     map_add' := by intros; ext i; fin_cases i <;> simp <;> ring
     map_smul' := by intros; ext i; fin_cases i <;> simp <;> ring
    } : Ambient→ₗ[ℝ] Ambient).toContinuousLinearMap

def rectangleInverse : Ambient→L[ℝ] Ambient :=
  ({ toFun := fun k => WithLp.toLp 2 ![k 2,k 0-k 2,k 1-k 2]
     map_add' := by intros; ext i; fin_cases i <;> simp <;> ring
     map_smul' := by intros; ext i; fin_cases i <;> simp <;> ring
    } : Ambient→ₗ[ℝ] Ambient).toContinuousLinearMap

theorem rectangleMap_inverse (k : Ambient) : rectangleMap (rectangleInverse k)=k := by
  ext i; fin_cases i <;> simp [rectangleMap,rectangleInverse]

theorem rectangleInverse_map (p : Ambient) : rectangleInverse (rectangleMap p)=p := by
  ext i; fin_cases i <;> simp [rectangleMap,rectangleInverse]

def criticalGauge (swap : Bool) (n m : ℤ) (p : Ambient) : Ambient :=
  if swap then PinnedLegAC.exchangeIncoming (rectangleMap p+latticeShift ![n,m,0])
  else rectangleMap p+latticeShift ![n,m,0]

theorem criticalGauge_energy (d : ℝ) (swap : Bool) (n m : ℤ) (p : Ambient) :
    liftedEnergy d (criticalGauge swap n m p)=PinnedLocalArea.rectangleEnergy d p := by
  cases swap <;> simp only [criticalGauge,Bool.false_eq_true,if_false,if_true]
  · exact liftedEnergy_lattice d ![n,m,0] (rectangleMap p)
  · rw [PinnedLegAC.energy_exchangeIncoming,liftedEnergy_lattice]
    rfl

theorem normalize_same_velocity {d y z : ℝ} (hd0 : 0<d) (hdU : d<1/2)
    (hv : velocity d y=velocity d z) :
    ∃ m : ℤ, ∃ v : ℝ, y=z+v+(m:ℝ)*period ∧
      (v=0 ∨ cos (z+v)≠cos z) ∧ velocity d (z+v)=velocity d z := by
  by_cases hc : cos y=cos z
  · obtain ⟨m,hm⟩ := trigonometric_pair_integer_shift hc
      (same_velocity_same_cos_sin hd0 hdU hv hc)
    exact ⟨m,0,by simpa only [add_zero] using hm,Or.inl rfl,by simp⟩
  · refine ⟨0,y-z,by simp,Or.inr ?_,?_⟩
    · simpa only [add_sub_cancel] using hc
    · simpa only [add_sub_cancel] using hv

/-- Every original critical point has a periodic trivial-pairing coordinate
whose remaining increment is either zero or a different point of the circle.
Thus the bad repeated-period axis does not enter the critical graph argument. -/
theorem every_critical_point_normalized {d : ℝ} (hd0 : 0<d) (hdU : d<1/2)
    {k : Ambient} (he : liftedEnergy d k=0) (hg : energyGradient d k=0) :
    ∃ swap : Bool, ∃ n m : ℤ, ∃ z v : ℝ,
      criticalGauge swap n m (WithLp.toLp 2 ![z,0,v])=k ∧
      (v=0 ∨ cos (z+v)≠cos z) ∧ velocity d (z+v)=velocity d z := by
  have h0 := congrArg (fun p : Ambient => p 0) hg
  have h1 := congrArg (fun p : Ambient => p 1) hg
  have h2 := congrArg (fun p : Ambient => p 2) hg
  change velocity d (k 0)-velocity d (k 0+k 1-k 2)=0 at h0
  change velocity d (k 1)-velocity d (k 0+k 1-k 2)=0 at h1
  change velocity d (k 0+k 1-k 2)-velocity d (k 2)=0 at h2
  have hv0 := (sub_eq_zero.mp h0).trans (sub_eq_zero.mp h2)
  have hv1 := (sub_eq_zero.mp h1).trans (sub_eq_zero.mp h2)
  rcases critical_integer_pairing hd0 hdU he hg with ⟨n,hn⟩ | ⟨n,hn⟩
  · obtain ⟨m,v,hv,hcase,hvel⟩ := normalize_same_velocity hd0 hdU hv1
    refine ⟨false,n,m,k 2,v,?_,hcase,hvel⟩
    ext i
    fin_cases i <;> simp [criticalGauge,rectangleMap,latticeShift,period] <;>
      dsimp [period] at hv <;> linarith
  · obtain ⟨m,v,hv,hcase,hvel⟩ := normalize_same_velocity hd0 hdU hv0
    refine ⟨true,n,m,k 2,v,?_,hcase,hvel⟩
    ext i
    fin_cases i <;> simp [criticalGauge,rectangleMap,latticeShift,period,
      PinnedLegAC.exchangeIncoming] <;> dsimp [period] at hv <;> linarith

theorem every_critical_point_factor_alternative {d : ℝ} (hd0 : 0<d) (hdU : d<1/2)
    {k : Ambient} (he : liftedEnergy d k=0) (hg : energyGradient d k=0) :
    ∃ swap : Bool, ∃ n m : ℤ, ∃ z v : ℝ,
      criticalGauge swap n m (WithLp.toLp 2 ![z,0,v])=k ∧
      (sharedFactor d (WithLp.toLp 2 ![z,0,v])≠0 ∨
        deriv (fun t : ℝ => sharedFactor d (WithLp.toLp 2 ![t,0,v])) z≠0) := by
  obtain ⟨swap,n,m,z,v,hk,hcase,hv⟩ := every_critical_point_normalized hd0 hdU he hg
  refine ⟨swap,n,m,z,v,hk,?_⟩
  rcases hcase with h0 | hc
  · subst v
    exact sharedFactor_origin_alternative hd0 hdU z
  · exact Or.inr (sharedFactor_separated_noncritical hd0 hdU hv hc).2

end
end Resonance.PinnedCriticalNormalization
