import Resonance.ActualLinftyCompact

/-! Explicit dictionary between the closed-cube subtype and the
ambient restricted-volume L-infinity space used by the physical form.
No boundary values are recovered from arbitrary L-infinity classes. -/
open MeasureTheory Set Filter
open scoped ENNReal Topology
namespace Resonance.CubeLinftyCoordinates
noncomputable section
set_option maxHeartbeats 900000
open ResonantMeasure ActualPairNormalization ActualReferenceRowOperator

theorem val_preserves (R : ℝ) :
    MeasurePreserving (Subtype.val : cube R → E) (cubeMeasure R) (cubeVolume R) :=
  ⟨measurable_subtype_coe,map_comap_subtype_coe (FiberContinuity.cube_isClosed R).measurableSet volume⟩

def restrict (R : ℝ) : Lp ℝ ∞ (cubeVolume R) →ₗᵢ[ℝ] Lp ℝ ∞ (cubeMeasure R) :=
  Lp.compMeasurePreservingₗᵢ ℝ Subtype.val (val_preserves R)

theorem restrict_ae (R : ℝ) (f : Lp ℝ ∞ (cubeVolume R)) :
    restrict R f =ᵐ[cubeMeasure R] (fun k : cube R => f (k:E)) :=
  Lp.coeFn_compMeasurePreserving f (val_preserves R)

def zeroExtension (R : ℝ) (f : C(cube R,ℝ)) : E → ℝ :=
  Function.extend Subtype.val f (fun _ => 0)

theorem zeroExtension_apply (R : ℝ) (f : C(cube R,ℝ)) (k : cube R) :
    zeroExtension R f k=f k := Subtype.val_injective.extend_apply _ _ _

theorem zeroExtension_measurable (R : ℝ) (f : C(cube R,ℝ)) :
    Measurable (zeroExtension R f) :=
  (MeasurableEmbedding.subtype_coe (FiberContinuity.cube_isClosed R).measurableSet).measurable_extend
    f.continuous.measurable measurable_const

theorem zeroExtension_bound (R : ℝ) (f : C(cube R,ℝ)) :
    ∀ᵐ k ∂cubeVolume R, ‖zeroExtension R f k‖ ≤ ‖f‖ := by
  filter_upwards [ae_restrict_mem (FiberContinuity.cube_isClosed R).measurableSet] with k hk
  rw [show zeroExtension R f k=f ⟨k,hk⟩ from zeroExtension_apply R f ⟨k,hk⟩]
  exact f.norm_coe_le_norm _

theorem zeroExtension_memLp (R : ℝ) (f : C(cube R,ℝ)) :
    MemLp (zeroExtension R f) ∞ (cubeVolume R) :=
  memLp_top_of_bound (zeroExtension_measurable R f).aestronglyMeasurable ‖f‖
    (zeroExtension_bound R f)

def extendVector (R : ℝ) (f : C(cube R,ℝ)) : Lp ℝ ∞ (cubeVolume R) :=
  (zeroExtension_memLp R f).toLp _

theorem extendVector_ae (R : ℝ) (f : C(cube R,ℝ)) :
    extendVector R f =ᵐ[cubeVolume R] zeroExtension R f :=
  (zeroExtension_memLp R f).coeFn_toLp

theorem extendVector_add (R : ℝ) (f g : C(cube R,ℝ)) :
    extendVector R (f+g)=extendVector R f+extendVector R g := by
  apply Lp.ext
  filter_upwards [extendVector_ae R (f+g),extendVector_ae R f,extendVector_ae R g,
    Lp.coeFn_add (extendVector R f) (extendVector R g),
    ae_restrict_mem (FiberContinuity.cube_isClosed R).measurableSet] with k hfg hf hg hs hk
  change (extendVector R f+extendVector R g) k=extendVector R f k+extendVector R g k at hs
  rw [hfg,hs,hf,hg]
  rw [zeroExtension_apply R (f+g) ⟨k,hk⟩,zeroExtension_apply R f ⟨k,hk⟩,
    zeroExtension_apply R g ⟨k,hk⟩]
  rfl

theorem extendVector_smul (R : ℝ) (a : ℝ) (f : C(cube R,ℝ)) :
    extendVector R (a • f)=a • extendVector R f := by
  apply Lp.ext
  filter_upwards [extendVector_ae R (a • f),extendVector_ae R f,
    Lp.coeFn_smul a (extendVector R f),
    ae_restrict_mem (FiberContinuity.cube_isClosed R).measurableSet] with k haf hf hs hk
  change (a • extendVector R f) k=a*extendVector R f k at hs
  rw [haf,hs,hf]
  rw [zeroExtension_apply R (a • f) ⟨k,hk⟩,zeroExtension_apply R f ⟨k,hk⟩]
  rfl

theorem extendVector_bound (R : ℝ) (f : C(cube R,ℝ)) : ‖extendVector R f‖ ≤ ‖f‖ := by
  rw [extendVector,Lp.norm_toLp,eLpNorm_exponent_top]
  have h := eLpNormEssSup_le_of_ae_bound (zeroExtension_bound R f)
  exact (ENNReal.toReal_le_toReal (zeroExtension_memLp R f).2.ne
    ENNReal.ofReal_ne_top).mpr h |>.trans_eq (ENNReal.toReal_ofReal (norm_nonneg f))

def extendLinear (R : ℝ) : C(cube R,ℝ) →ₗ[ℝ] Lp ℝ ∞ (cubeVolume R) where
  toFun := extendVector R
  map_add' := extendVector_add R
  map_smul' := extendVector_smul R

def embed (R : ℝ) : C(cube R,ℝ) →L[ℝ] Lp ℝ ∞ (cubeVolume R) :=
  (extendLinear R).mkContinuous 1 (fun f => by simpa only [one_mul] using extendVector_bound R f)

theorem embed_ae (R : ℝ) (f : C(cube R,ℝ)) :
    embed R f =ᵐ[cubeVolume R] zeroExtension R f := extendVector_ae R f

theorem restrict_embed (R : ℝ) (f : C(cube R,ℝ)) :
    restrict R (embed R f)=ActualLinftyCompact.continuousToLinfty R f := by
  apply Lp.ext
  filter_upwards [restrict_ae R (embed R f),
    (val_preserves R).quasiMeasurePreserving.ae_eq (embed_ae R f),
    ActualLinftyCompact.continuousToLinfty_ae R f] with k hr he ht
  exact hr.trans ((he.trans (zeroExtension_apply R f k)).trans ht.symm)

end
end Resonance.CubeLinftyCoordinates
