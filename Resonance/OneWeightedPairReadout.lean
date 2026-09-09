import Resonance.ActualPairWeightSmooth

/-! One genuinely frequency-weighted input in each actual pair row.
This is an input to the full cubic reconstruction, not a replacement
of the original collision by two independent pair models. -/
open MeasureTheory Set
open scoped ENNReal ContDiff
namespace Resonance.OneWeightedPairReadout
noncomputable section
set_option maxHeartbeats 1800000
open ResonantMeasure CollisionFrequency ActualPairNormalization
open QuartetWeightSpace ActualPairWeightLinear LinftyMultiplication

def referenceContinuous {R : ℝ} (hR : 0≤R) : C(cube R,ℝ) :=
  ⟨fun k=>referenceFrequency R k,(referenceFrequency_continuousOn hR).restrict⟩

def weightedInput {R : ℝ} (hR : 0≤R) (u : C(cube R,ℝ)) : X R :=
  CubeLinftyCoordinates.embed R (referenceContinuous hR*u)

theorem weightedInput_ae {R : ℝ} (hR : 0≤R) (u : C(cube R,ℝ)) :
    weightedInput hR u=ᵐ[cubeVolume R] fun k=>
      referenceFrequency R k*CubeLinftyCoordinates.zeroExtension R u k := by
  filter_upwards [CubeLinftyCoordinates.embed_ae R (referenceContinuous hR*u),
    ae_restrict_mem (measurable_cube R)] with k he hk
  change weightedInput hR u k=_ at he
  rw [he,CubeLinftyCoordinates.zeroExtension_apply R _ ⟨k,hk⟩,
    CubeLinftyCoordinates.zeroExtension_apply R u ⟨k,hk⟩]
  rfl

theorem weightedInput_bound {R : ℝ} (hR : 0≤R) (u : C(cube R,ℝ)) :
    ‖weightedInput hR u‖≤‖referenceContinuous hR*u‖ :=
  CubeLinftyCoordinates.extendVector_bound R _

def twoWeight (R : ℝ) (i j : Fin 4) (g h : C(cube R,ℝ)) : WeightSpace R :=
  legPullback R i g*legPullback R j h

theorem legPullback_bound (R : ℝ) (i : Fin 4) (g : C(cube R,ℝ)) :
    ‖legPullback R i g‖≤‖g‖ := by
  apply (ContinuousMap.norm_le _ (norm_nonneg g)).mpr
  intro q
  exact g.norm_coe_le_norm (q i)

theorem twoWeight_bound (R : ℝ) (i j : Fin 4) (g h : C(cube R,ℝ)) :
    ‖twoWeight R i j g h‖≤‖g‖*‖h‖ := by
  apply (norm_mul_le _ _).trans
  exact mul_le_mul (legPullback_bound R i g) (legPullback_bound R j h)
    (norm_nonneg _) (norm_nonneg _)

def incomingReadout {R : ℝ} (hR : 0<R) (i j : Fin 4) (u g h : C(cube R,ℝ)) : X R :=
  incomingOperator hR (twoWeight R i j g h) (weightedInput hR.le u)

def crossReadout {R : ℝ} (hR : 0<R) (i j : Fin 4) (u g h : C(cube R,ℝ)) : X R :=
  crossOperator hR (twoWeight R i j g h) (weightedInput hR.le u)

theorem incomingReadout_bound {R : ℝ} (hR : 0<R) (i j : Fin 4) (u g h : C(cube R,ℝ)) :
    ‖incomingReadout hR i j u g h‖≤rowBound hR*‖referenceContinuous hR.le*u‖*‖g‖*‖h‖ := by
  have h1 := (incomingOperator hR (twoWeight R i j g h)).le_opNorm (weightedInput hR.le u)
  have h2 := (incomingOperator hR).le_opNorm (twoWeight R i j g h)
  have h3 : ‖incomingOperator hR (twoWeight R i j g h)‖≤rowBound hR*(‖g‖*‖h‖) :=
    h2.trans (mul_le_mul (incomingOperator_norm_le hR) (twoWeight_bound R i j g h)
      (norm_nonneg _) (rowBound_nonnegative hR))
  exact h1.trans ((mul_le_mul h3 (weightedInput_bound hR.le u) (norm_nonneg _)
    (mul_nonneg (rowBound_nonnegative hR) (mul_nonneg (norm_nonneg g) (norm_nonneg h)))).trans_eq (by ring))

theorem crossReadout_bound {R : ℝ} (hR : 0<R) (i j : Fin 4) (u g h : C(cube R,ℝ)) :
    ‖crossReadout hR i j u g h‖≤rowBound hR*‖referenceContinuous hR.le*u‖*‖g‖*‖h‖ := by
  have h1 := (crossOperator hR (twoWeight R i j g h)).le_opNorm (weightedInput hR.le u)
  have h2 := (crossOperator hR).le_opNorm (twoWeight R i j g h)
  have h3 : ‖crossOperator hR (twoWeight R i j g h)‖≤rowBound hR*(‖g‖*‖h‖) :=
    h2.trans (mul_le_mul (crossOperator_norm_le hR) (twoWeight_bound R i j g h)
      (norm_nonneg _) (rowBound_nonnegative hR))
  exact h1.trans ((mul_le_mul h3 (weightedInput_bound hR.le u) (norm_nonneg _)
    (mul_nonneg (rowBound_nonnegative hR) (mul_nonneg (norm_nonneg g) (norm_nonneg h)))).trans_eq (by ring))

theorem incomingReadout_ae {R : ℝ} (hR : 0<R) (i j : Fin 4) (u g h : C(cube R,ℝ)) :
    incomingReadout hR i j u g h=ᵐ[cubeVolume R] fun k=>∫p,
      (‖k-p‖/8)*(∫σ,rawWeight R (twoWeight R i j g h)
        (IncomingPairMarginal.incomingQuartet ((k,p),σ))∂surface)*
          CubeLinftyCoordinates.zeroExtension R u p∂cubeVolume R := by
  filter_upwards [incomingOperator_ae hR (twoWeight R i j g h) (weightedInput hR.le u)] with k hk
  change incomingReadout hR i j u g h k=_ at hk
  rw [hk]
  apply integral_congr_ae
  filter_upwards [weightedInput_ae hR.le u,CornerInverseFrequency.referenceFrequency_positive_ae hR]
    with p hu hp
  rw [hu]
  unfold incomingKernel PairWeightLinear.kernel PairWeightLinear.fiber incomingFactor
  field_simp

theorem crossReadout_ae {R : ℝ} (hR : 0<R) (i j : Fin 4) (u g h : C(cube R,ℝ)) :
    crossReadout hR i j u g h=ᵐ[cubeVolume R] fun k=>∫p,
      (2*‖p-k‖)⁻¹*(∫z,rawWeight R (twoWeight R i j g h)
        (CrossPairCoordinates.crossQuartet ((k,p),z))∂CrossRowPointwise.finitePlaneMeasure R)*
          CubeLinftyCoordinates.zeroExtension R u p∂cubeVolume R := by
  filter_upwards [crossOperator_ae hR (twoWeight R i j g h) (weightedInput hR.le u)] with k hk
  change crossReadout hR i j u g h k=_ at hk
  rw [hk]
  apply integral_congr_ae
  filter_upwards [weightedInput_ae hR.le u,CornerInverseFrequency.referenceFrequency_positive_ae hR]
    with p hu hp
  rw [hu]
  unfold crossKernel PairWeightLinear.kernel PairWeightLinear.fiber crossFactor
  field_simp

end
end Resonance.OneWeightedPairReadout
