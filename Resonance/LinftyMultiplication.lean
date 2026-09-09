import Resonance.NormalizedFiberMultilinear

/-! Bounded multiplication on the actual ambient cube L-infinity space,
linear in the multiplier. This permits Banach inverse differentiation of
the positive normalized loss without asserting corner continuity. -/
open MeasureTheory Set
open scoped ENNReal
namespace Resonance.LinftyMultiplication
noncomputable section
set_option maxHeartbeats 1200000
open ResonantMeasure ActualPairNormalization CubeLinftyMultiplier

abbrev X (R : ℝ) := Lp ℝ ∞ (cubeVolume R)

def multiply (R : ℝ) (f : X R) : X R→L[ℝ]X R := operator (Lp.memLp f)

theorem multiply_ae (R : ℝ) (f g : X R) :
    multiply R f g=ᵐ[cubeVolume R] fun k=>g k*f k := operator_ae (Lp.memLp f) g

theorem multiply_norm_le (R : ℝ) (f : X R) : ‖multiply R f‖≤‖f‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro g
  exact vector_bound (Lp.memLp f) (norm_nonneg _) (LinftyRowOperator.ae_norm_bound f) g

theorem multiply_add (R : ℝ) (f g : X R) :
    multiply R (f+g)=multiply R f+multiply R g := by
  ext h
  filter_upwards [multiply_ae R (f+g) h,multiply_ae R f h,multiply_ae R g h,
    Lp.coeFn_add f g,Lp.coeFn_add (multiply R f h) (multiply R g h)] with k hfg hf hg hi ho
  change (f+g) k=f k+g k at hi
  change (multiply R f h+multiply R g h) k=multiply R f h k+multiply R g h k at ho
  change multiply R (f+g) h k=(multiply R f h+multiply R g h) k
  rw [hfg,ho,hi,hf,hg,mul_add]

theorem multiply_smul (R : ℝ) (c : ℝ) (f : X R) :
    multiply R (c • f)=c • multiply R f := by
  ext h
  filter_upwards [multiply_ae R (c • f) h,multiply_ae R f h,
    Lp.coeFn_smul c f,Lp.coeFn_smul c (multiply R f h)] with k hcf hf hi ho
  simp only [Pi.smul_apply,smul_eq_mul] at hi ho
  change multiply R (c • f) h k=(c • multiply R f h) k
  rw [hcf,ho,hi,hf]
  ring

def linear (R : ℝ) : X R→ₗ[ℝ](X R→L[ℝ]X R) where
  toFun := multiply R
  map_add' := multiply_add R
  map_smul' := multiply_smul R

def operatorMap (R : ℝ) : X R→L[ℝ](X R→L[ℝ]X R) :=
  (linear R).mkContinuous 1 (fun f=>by simpa using multiply_norm_le R f)

theorem operatorMap_apply_ae (R : ℝ) (f g : X R) :
    operatorMap R f g=ᵐ[cubeVolume R] fun k=>g k*f k := multiply_ae R f g

theorem operatorMap_norm_le (R : ℝ) : ‖operatorMap R‖≤1 :=
  LinearMap.mkContinuous_norm_le _ zero_le_one _

theorem composition_eq_identity (R : ℝ) (f g : X R)
    (he : ∀ᵐk∂cubeVolume R,f k*g k=1) :
    (operatorMap R f).comp (operatorMap R g)=1 := by
  ext h
  filter_upwards [operatorMap_apply_ae R f (operatorMap R g h),operatorMap_apply_ae R g h,he]
    with k hf hg hk
  change operatorMap R f (operatorMap R g h) k=h k
  rw [hf,hg]
  calc
    _=h k*(f k*g k) := by ring
    _=h k := by rw [hk,mul_one]

def unit (R : ℝ) (f g : X R) (he : ∀ᵐk∂cubeVolume R,f k*g k=1) : (X R→L[ℝ]X R)ˣ where
  val := operatorMap R f
  inv := operatorMap R g
  val_inv := composition_eq_identity R f g he
  inv_val := composition_eq_identity R g f (he.mono (fun _ h=>by simpa only [mul_comm] using h))

theorem inverse_operatorMap (R : ℝ) (f g : X R)
    (he : ∀ᵐk∂cubeVolume R,f k*g k=1) :
    Ring.inverse (operatorMap R f)=operatorMap R g := Ring.inverse_unit (unit R f g he)

end
end Resonance.LinftyMultiplication
