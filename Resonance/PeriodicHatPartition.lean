import Resonance.PinnedCompactLocalization
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Topology.Algebra.Support

/-! An explicit finite compact partition of the original period cell. The
hat is continuous at cell seams, so no discontinuous cell indicator is
submitted to the compact-source coarea theorem. -/
open Set MeasureTheory
open scoped BigOperators
namespace Resonance.PeriodicHatPartition
noncomputable section
open PinnedMeasure PinnedPeriodicity PinnedCompactLocalization

def hat (t : ℝ) : ℝ := max 0 (1-|t|/period)

theorem hat_continuous : Continuous hat := by unfold hat; fun_prop

theorem hat_nonneg (t : ℝ) : 0≤hat t := le_max_left _ _

theorem hat_eq_zero_of_le {t : ℝ} (ht : period≤|t|) : hat t=0 := by
  unfold hat
  apply max_eq_left
  have h : (1:ℝ)≤|t|/period := (le_div_iff₀ period_pos).mpr (by simpa using ht)
  linarith

theorem hat_two_sum {t : ℝ} (ht : t∈Icc 0 period) : hat t+hat (t-period)=1 := by
  have ht0 : 0≤t := ht.1
  have h1 : 0≤1-t/period := by
    have h := (div_le_one period_pos).mpr ht.2
    linarith
  have h2 : 0≤1-(period-t)/period := by
    have h := (div_le_one period_pos).mpr (by linarith : period-t≤period)
    linarith
  simp only [hat,abs_of_nonneg ht.1,abs_of_nonpos (sub_nonpos.mpr ht.2),neg_sub,
    max_eq_right h1,max_eq_right h2]
  field_simp [ne_of_gt period_pos]
  ring

abbrev Index := Fin 3 → Fin 2

def winding (i : Index) : Fin 3 → ℤ := fun j=>-(i j : ℤ)

def weight (k : Ambient) : ℝ := ∏j:Fin 3,hat (k j)

theorem weight_continuous : Continuous weight := by
  apply continuous_finset_prod
  intro j _
  exact hat_continuous.comp (PiLp.continuous_apply 2 (fun _ : Fin 3=>ℝ) j)

theorem weight_nonneg (k : Ambient) : 0≤weight k := Finset.prod_nonneg (fun j _=>hat_nonneg (k j))

theorem weight_lattice (i : Index) (k : Ambient) :
    weight (translation (winding i) k)=∏j:Fin 3,hat (k j-(i j : ℝ)*period) := by
  simp only [weight,translation_apply]
  apply Finset.prod_congr rfl
  intro j _
  congr 1
  simp [latticeShift,winding,PiLp.add_apply,sub_eq_add_neg]

theorem weight_finite_partition {k : Ambient} (hk : k∈fundamentalCell) :
    (∑i:Index,weight (translation (winding i) k))=1 := by
  simp_rw [weight_lattice]
  have he := Fintype.prod_sum (fun (j : Fin 3) (i : Fin 2)=>hat (k j-(i : ℝ)*period))
  rw [←he]
  have hs : ∀j:Fin 3,(∑i:Fin 2,hat (k j-(i : ℝ)*period))=1 := by
    intro j
    simpa using hat_two_sum ⟨(hk j).1,(hk j).2.le⟩
  simp_rw [hs]
  simp

end
end Resonance.PeriodicHatPartition
