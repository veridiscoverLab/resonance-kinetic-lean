import Resonance.ActualComplexNormalization
import Resonance.CompactHilbertGap

/-! All constants required by the Fourier compensation are derived from
the original five-moment matrices on compact positive RJ parameter sets. -/
open Set
namespace Resonance.ActualUniformHilbertData
noncomputable section
set_option maxHeartbeats 800000
open Thermodynamics MatrixHilbertDictionary ActualComplexNormalization
open RankTwoHilbert HilbertQuadraticBounds

abbrev W := EuclideanSpace ℝ (Fin 3)
abbrev UnitDirection := Metric.sphere (0 : W) 1

theorem unit_direction_nonzero (w : UnitDirection) : (fun i=>w.val i)≠0 := by
  intro hz
  have he : w.val=0 := by ext i; exact congrFun hz i
  simpa [he] using w.property

theorem direction_coordinates_continuous :
    Continuous (fun w : UnitDirection=>(fun i=>w.val i)) := by
  apply continuous_pi
  intro i
  exact (PiLp.proj 2 (fun _ : Fin 3=>ℝ) i : W→L[ℝ]ℝ).continuous.comp continuous_subtype_val

theorem actual_uniform_hilbert_data {R : ℝ} (hR : 0 < R) {K : Set Parameter}
    (hK : IsCompact K) (hpos : K⊆positiveDomain R) :
    ∃β k L : ℝ,0 < β ∧ 0 < k ∧ 0 < L ∧ ∀θ : K,∀w : UnitDirection,
      ‖A R θ (fun i=>w.val i)‖ ≤ L ∧
      ‖B hR (hpos θ.property) (fun i=>w.val i)‖ ≤ L ∧
      k ≤ ‖b R θ (fun i=>w.val i)‖^2 ∧
      ∀v : H,β*‖micro (e R θ) v‖^2 ≤
        quadratic (B hR (hpos θ.property) (fun i=>w.val i)) v := by
  letI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  letI : CompactSpace UnitDirection := isCompact_iff_compactSpace.mp (isCompact_sphere (0 : W) 1)
  let P := K×UnitDirection
  let Af : P→H→L[ℂ]H := fun p=>A R p.1 (fun i=>p.2.val i)
  let Bf : P→H→L[ℂ]H := fun p=>B hR (hpos p.1.property) (fun i=>p.2.val i)
  let ef : P→H := fun p=>e R p.1
  let bf : P→H := fun p=>b R p.1 (fun i=>p.2.val i)
  have hθmap : Continuous (fun θ : K=>(⟨θ.val,hpos θ.property⟩ : positiveDomain R)) :=
    continuous_subtype_val.subtype_mk _
  have hm : Continuous (fun p : P=>
      ((⟨p.1.val,hpos p.1.property⟩ : positiveDomain R),fun i=>p.2.val i)) :=
    (hθmap.comp continuous_fst).prodMk (direction_coordinates_continuous.comp continuous_snd)
  have hAc : Continuous Af := by
    exact Continuous.comp
      (g := fun p : positiveDomain R×(Fin 3→ℝ)=>A R p.1 p.2)
      (f := fun p : P=>((⟨p.1.val,hpos p.1.property⟩ : positiveDomain R),fun i=>p.2.val i))
      (original_A_continuous hR) hm
  have hBc : Continuous Bf := by
    exact Continuous.comp
      (g := fun p : positiveDomain R×(Fin 3→ℝ)=>B hR p.1.property p.2)
      (f := fun p : P=>((⟨p.1.val,hpos p.1.property⟩ : positiveDomain R),fun i=>p.2.val i))
      (original_B_continuous hR) hm
  have hec : Continuous ef := by
    exact Continuous.comp (g := fun θ : positiveDomain R=>e R θ)
      (f := fun p : P=>(⟨p.1.val,hpos p.1.property⟩ : positiveDomain R))
      (original_e_continuous hR) (hθmap.comp continuous_fst)
  have hbc : Continuous bf := by
    exact Continuous.comp
      (g := fun p : positiveDomain R×(Fin 3→ℝ)=>b R p.1 p.2)
      (f := fun p : P=>((⟨p.1.val,hpos p.1.property⟩ : positiveDomain R),fun i=>p.2.val i))
      (original_b_continuous hR) hm
  obtain ⟨β,hβ,hgap⟩ := CompactHilbertGap.uniform_micro_gap Bf ef hBc hec
    (fun p=>original_B_selfAdjoint hR (hpos p.1.property) _)
    (fun p=>original_e_unit hR (hpos p.1.property))
    (fun p=>original_B_mass_zero hR (hpos p.1.property) (unit_direction_nonzero p.2))
    (fun p v=>original_B_nonneg hR (hpos p.1.property) _ v)
    (fun p v=>original_B_zero_iff hR (hpos p.1.property) _ v)
    (fun p v=>original_complex_kernel hR (hpos p.1.property) (unit_direction_nonzero p.2) v)
  let U : P→ℝ := fun p=>‖Af p‖+‖Bf p‖+1
  let V : P→ℝ := fun p=>‖bf p‖^2
  have hUc : Continuous U := (hAc.norm.add hBc.norm).add continuous_const
  have hVc : Continuous V := hbc.norm.pow 2
  have hUp : ∀p,0 < U p := by
    intro p
    have ha := norm_nonneg (Af p)
    have hb := norm_nonneg (Bf p)
    change 0 < ‖Af p‖+‖Bf p‖+1
    linarith
  have hVp : ∀p,0 < V p := by
    intro p
    apply sq_pos_of_pos
    exact norm_pos_iff.mpr (original_b_nonzero hR (hpos p.1.property) (unit_direction_nonzero p.2))
  by_cases hn : (univ : Set P).Nonempty
  · obtain ⟨p,_,hmin⟩ := (isCompact_univ : IsCompact (univ : Set P)).exists_isMinOn hn hVc.continuousOn
    obtain ⟨q,_,hmax⟩ := (isCompact_univ : IsCompact (univ : Set P)).exists_isMaxOn hn hUc.continuousOn
    refine ⟨β,V p,U q,hβ,hVp p,hUp q,?_⟩
    intro θ w
    have hu : U (θ,w) ≤ U q := @hmax (θ,w) (mem_univ _)
    have hv : V p ≤ V (θ,w) := @hmin (θ,w) (mem_univ _)
    have ha := norm_nonneg (Af (θ,w))
    have hb := norm_nonneg (Bf (θ,w))
    change ‖Af (θ,w)‖ ≤ U q ∧ ‖Bf (θ,w)‖ ≤ U q ∧ V p ≤ V (θ,w) ∧
      ∀v,β*‖micro (ef (θ,w)) v‖^2 ≤ quadratic (Bf (θ,w)) v
    refine ⟨?_,?_,hv,fun v=>hgap (θ,w) v⟩ <;>
      change ‖Af (θ,w)‖+‖Bf (θ,w)‖+1 ≤ U q at hu <;> linarith
  · refine ⟨β,1,1,hβ,by norm_num,by norm_num,?_⟩
    intro θ w
    exact (hn ⟨(θ,w),mem_univ _⟩).elim

end
end Resonance.ActualUniformHilbertData
