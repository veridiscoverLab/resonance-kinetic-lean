import Resonance.PolarCoordinates

/-! The exact six-dimensional Jacobian for the two incoming legs, used
to identify the actual off-diagonal pair marginal of the full quartet.
The map is (V,w) -> (V+w,V-w), with volume factor 1/8. -/
open MeasureTheory Matrix
open scoped ENNReal Matrix Kronecker
namespace Resonance.PairCoordinates
noncomputable section
open ResonantMeasure
abbrev PairIndex := Fin 2 × Fin 3
abbrev Six := PairIndex→ℝ

def block : Matrix (Fin 2) (Fin 2) ℝ := !![1,1;1,-1]
def matrix : Matrix PairIndex PairIndex ℝ := block⊗ₖ(1 : Matrix (Fin 3) (Fin 3) ℝ)
def linear : Six→ₗ[ℝ]Six := Matrix.toLin' matrix

theorem matrix_det : matrix.det = -8 := by
  rw [matrix,Matrix.det_kronecker]
  norm_num [block,Matrix.det_fin_two]

theorem linear_zero (z : Six) (j : Fin 3) : linear z (0,j)=z (0,j)+z (1,j) := by
  fin_cases j <;> simp [linear,matrix,Matrix.toLin'_apply,Matrix.mulVec,dotProduct,
    Fintype.sum_prod_type,block,Fin.sum_univ_succ,Matrix.one_apply]

theorem linear_one (z : Six) (j : Fin 3) : linear z (1,j)=z (0,j)-z (1,j) := by
  fin_cases j <;> simp [linear,matrix,Matrix.toLin'_apply,Matrix.mulVec,dotProduct,
    Fintype.sum_prod_type,block,Fin.sum_univ_succ,Matrix.one_apply,sub_eq_add_neg]

theorem linear_measurable : Measurable linear :=
  linear.continuous_of_finiteDimensional.measurable

theorem linear_volume : Measure.map linear (volume : Measure Six)=
    ENNReal.ofReal (1/8 : ℝ) • (volume : Measure Six) := by
  have hn : matrix.det≠0 := by rw [matrix_det]; norm_num
  simpa [linear,matrix_det] using Real.map_matrix_volume_pi_eq_smul_volume_pi hn

def currySix : Six≃ᵐ(Fin 2→Fin 3→ℝ) := MeasurableEquiv.curry (Fin 2) (Fin 3) ℝ

theorem currySix_preserves_volume : MeasurePreserving currySix volume volume := by
  apply MeasurePreserving.symm currySix.symm
  refine ⟨currySix.symm.measurable,?_⟩
  apply (Measure.pi_eq ?_).symm
  intro s hs
  rw [MeasurableEquiv.map_apply]
  have he : currySix.symm ⁻¹' (Set.univ.pi s)=
      Set.univ.pi (fun i : Fin 2=>Set.univ.pi (fun j : Fin 3=>s (i,j))) := by
    ext x
    simp [currySix,Set.mem_pi,Function.uncurry,Prod.forall]
  rw [he]
  change (Measure.pi (fun _ : Fin 2=>Measure.pi (fun _ : Fin 3=>(volume : Measure ℝ))))
    (Set.univ.pi (fun i : Fin 2=>Set.univ.pi (fun j : Fin 3=>s (i,j))))=_
  rw [Measure.pi_pi]
  simp_rw [Measure.pi_pi]
  exact (Fintype.prod_prod_type (fun p : PairIndex=>(volume : Measure ℝ) (s p))).symm

def sixToPair (z : Six) : E×E :=
  (WithLp.toLp 2 (fun j=>z (0,j)),WithLp.toLp 2 (fun j=>z (1,j)))

theorem sixToPair_preserves_volume :
    MeasurePreserving sixToPair (volume : Measure Six) ((volume : Measure E).prod volume) := by
  have hp := volume_preserving_pi (fun _ : Fin 2=>PiLp.volume_preserving_toLp (Fin 3))
  exact (volume_preserving_piFinTwo (fun _ : Fin 2=>E)).comp
    (hp.comp currySix_preserves_volume)

def pairMap (p : E×E) : E×E := (p.1+p.2,p.1-p.2)

theorem pairMap_measurable : Measurable pairMap := by unfold pairMap; fun_prop

theorem pairMap_coordinates (z : Six) : pairMap (sixToPair z)=sixToPair (linear z) := by
  apply Prod.ext
  · ext j
    exact (linear_zero z j).symm
  · ext j
    exact (linear_one z j).symm

theorem pairMap_volume : Measure.map pairMap ((volume : Measure E).prod volume)=
    ENNReal.ofReal (1/8 : ℝ) • ((volume : Measure E).prod volume) := by
  rw [←sixToPair_preserves_volume.map_eq,
    Measure.map_map pairMap_measurable sixToPair_preserves_volume.measurable]
  have he : pairMap∘sixToPair=sixToPair∘linear := funext pairMap_coordinates
  rw [he,←Measure.map_map sixToPair_preserves_volume.measurable linear_measurable,
    linear_volume,Measure.map_smul,sixToPair_preserves_volume.map_eq]

theorem pairMap_quasiMeasurePreserving : Measure.QuasiMeasurePreserving pairMap
    ((volume : Measure E).prod volume) ((volume : Measure E).prod volume) := by
  refine ⟨pairMap_measurable,?_⟩
  rw [pairMap_volume]
  intro s hs
  simp [Measure.smul_apply,hs]

end
end Resonance.PairCoordinates
