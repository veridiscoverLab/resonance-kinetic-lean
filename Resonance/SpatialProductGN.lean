import Resonance.SpatialMomentumSections

/-! Spatial products of actual derivatives at several momentum legs.
All factors use the same spatial point and the same compatible kinetic
field; the subsequent momentum estimate uses the original joint measure. -/
open Set MeasureTheory Filter
open scoped Topology ENNReal
namespace Resonance.SpatialProductGN
noncomputable section
open ResonantMeasure WeightedJointMeasure FrequencyWeightedForm
open FreeTransport SpatialChainRule SpatialJetSpace SpatialTranslationOrbit
open SpatialIntegrationByParts SpatialThirdGN MixedSpatialGN SpatialMomentumSections
set_option maxHeartbeats 1500000

theorem abs_cube_two_thirds (x : ℝ) : (|x|^3)^((2:ℝ)/3)=x^2 := by
  rw [←Real.rpow_natCast,←Real.rpow_mul (abs_nonneg x)]
  norm_num [Real.rpow_two,sq_abs]

theorem sixth_one_third (x : ℝ) : (x^6)^((1:ℝ)/3)=x^2 := by
  have he : x^6=|x|^6 := by
    rw [show (6:ℕ)=2*3 by norm_num,pow_mul,pow_mul,sq_abs]
  rw [he,←Real.rpow_natCast,←Real.rpow_mul (abs_nonneg x)]
  norm_num [Real.rpow_two,sq_abs]

theorem two_one_product_holder (d e : ScalarField) :
    integralCLM ((d*e)^2) ≤
      (integralCLM ((absField d)^3))^((2:ℝ)/3)*(integralCLM (e^6))^((1:ℝ)/3) := by
  have h:=JointCornerHolder.holder_two_one (scalar_integrable ((absField d)^3))
    (scalar_integrable (e^6)) (fun X=>pow_nonneg (abs_nonneg (d X)) 3)
    (fun X=>by change 0 ≤ (e X)^6; positivity)
  have he : (fun X:SpatialTorus=>(((absField d)^3) X)^((2:ℝ)/3)*((e^6) X)^((1:ℝ)/3))=
      (fun X=>((d*e)^2) X) := by
    funext X
    change (|d X|^3)^((2:ℝ)/3)*((e X)^6)^((1:ℝ)/3)=(d X*e X)^2
    rw [abs_cube_two_thirds,sixth_one_third,mul_pow]
  rw [he] at h
  exact h

theorem sixth_nonnegative (f : ScalarField) : 0 ≤ integralCLM (f^6) := by
  apply integral_nonneg
  intro X
  change 0 ≤ (f X)^6
  positivity

theorem three_product_holder (d e f : ScalarField) :
    integralCLM ((d*e*f)^2) ≤ (integralCLM (d^6))^((1:ℝ)/3)*
      (integralCLM (e^6))^((1:ℝ)/3)*(integralCLM (f^6))^((1:ℝ)/3) := by
  have h:=two_one_product_holder (d*e) f
  have hc:=integral_cauchy ((absField d)^3) ((absField e)^3)
  have he : (absField (d*e))^3=(absField d)^3*(absField e)^3 := by
    ext X
    change |d X*e X|^3=|d X|^3*|e X|^3
    rw [abs_mul,mul_pow]
  have hsq (g : ScalarField) : ((absField g)^3)^2=g^6 := by
    ext X
    change (|g X|^3)^2=(g X)^6
    rw [←pow_mul,show 3*2=2*3 by norm_num,pow_mul,sq_abs]
    ring
  have hn : 0 ≤ integralCLM ((absField d)^3*(absField e)^3) := by
    apply integral_nonneg
    intro X
    exact mul_nonneg (pow_nonneg (abs_nonneg _) 3) (pow_nonneg (abs_nonneg _) 3)
  rw [abs_of_nonneg hn,hsq,hsq] at hc
  rw [he] at h
  apply h.trans
  have hb:=mul_le_mul_of_nonneg_right
    (Real.rpow_le_rpow hn hc (by norm_num : (0:ℝ)≤2/3))
    (Real.rpow_nonneg (sixth_nonnegative f) ((1:ℝ)/3))
  have hr : (Real.sqrt (integralCLM (d^6))*Real.sqrt (integralCLM (e^6)))^((2:ℝ)/3)=
      (integralCLM (d^6))^((1:ℝ)/3)*(integralCLM (e^6))^((1:ℝ)/3) := by
    rw [Real.mul_rpow (Real.sqrt_nonneg _) (Real.sqrt_nonneg _),
      Real.sqrt_eq_rpow,Real.sqrt_eq_rpow,←Real.rpow_mul (sixth_nonnegative d),
      ←Real.rpow_mul (sixth_nonnegative e)]
    norm_num
  simpa only [hr] using hb

def twoOneConstant (M : ℝ) : ℝ:=(35640*M)^((2:ℝ)/3)*(2500*M^4)^((1:ℝ)/3)

theorem twoOneConstant_nonneg {M : ℝ} (hM : 0 ≤ M) : 0 ≤ twoOneConstant M := by
  unfold twoOneConstant
  positivity

theorem actual_two_one_spatial {R : ℝ} (p : JetSpace R) (k l : E)
    (i j n : Fin 3) {M : ℝ} (hM : 0 ≤ M)
    (hk : amplitude p k ≤ M) (hl : amplitude p l ≤ M) :
    (∫X,(evaluate (secondCubeSection p i j) X k*evaluate (firstCubeSection p n) X l)^2) ≤
      twoOneConstant M*(mass p k)^((2:ℝ)/3)*(mass p l)^((1:ℝ)/3) := by
  let d:=zeroSection (secondCubeSection p i j) k
  let e:=zeroSection (firstCubeSection p n) l
  have h:=two_one_product_holder d e
  have hd : integralCLM ((absField d)^3) ≤35640*M*mass p k := by
    exact (ambient_coordinate_GN p k i j).2.trans
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hk (by norm_num))
        (mass_nonnegative p k))
  have he : integralCLM (e^6) ≤2500*M^4*mass p l := by
    exact (ambient_coordinate_GN p l n n).1.trans
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (norm_nonneg _) hl 4) (by norm_num)) (mass_nonnegative p l))
  have hdn : 0 ≤ integralCLM ((absField d)^3) :=
    integral_nonneg (fun X=>pow_nonneg (abs_nonneg (d X)) 3)
  have hb:=mul_le_mul
    (Real.rpow_le_rpow hdn hd (by norm_num : (0:ℝ)≤2/3))
    (Real.rpow_le_rpow (sixth_nonnegative e) he (by norm_num : (0:ℝ)≤1/3))
    (Real.rpow_nonneg (sixth_nonnegative e) _)
    (Real.rpow_nonneg (mul_nonneg (mul_nonneg (by norm_num) hM) (mass_nonnegative p k)) _)
  have hr : (35640*M*mass p k)^((2:ℝ)/3)*(2500*M^4*mass p l)^((1:ℝ)/3)=
      twoOneConstant M*(mass p k)^((2:ℝ)/3)*(mass p l)^((1:ℝ)/3) := by
    rw [Real.mul_rpow (by positivity : 0 ≤ 35640*M) (mass_nonnegative p k),
      Real.mul_rpow (by positivity : 0 ≤ 2500*M^4) (mass_nonnegative p l)]
    unfold twoOneConstant
    ring
  exact h.trans (hb.trans_eq hr)

theorem actual_three_spatial {R : ℝ} (p : JetSpace R) (k l m : E)
    (i j n : Fin 3) {M : ℝ}
    (hk : amplitude p k ≤ M) (hl : amplitude p l ≤ M) (hm : amplitude p m ≤ M) :
    (∫X,(evaluate (firstCubeSection p i) X k*evaluate (firstCubeSection p j) X l*
      evaluate (firstCubeSection p n) X m)^2) ≤
      2500*M^4*(mass p k)^((1:ℝ)/3)*(mass p l)^((1:ℝ)/3)*(mass p m)^((1:ℝ)/3) := by
  let d:=zeroSection (firstCubeSection p i) k
  let e:=zeroSection (firstCubeSection p j) l
  let f:=zeroSection (firstCubeSection p n) m
  have hg (a:E) (b:Fin 3) (ha:amplitude p a ≤ M) :
      integralCLM ((zeroSection (firstCubeSection p b) a)^6) ≤2500*M^4*mass p a := by
    exact (ambient_coordinate_GN p a b b).1.trans
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (norm_nonneg _) ha 4) (by norm_num)) (mass_nonnegative p a))
  have h:=three_product_holder d e f
  have h1:=Real.rpow_le_rpow (sixth_nonnegative d) (hg k i hk) (by norm_num : (0:ℝ)≤1/3)
  have h2:=Real.rpow_le_rpow (sixth_nonnegative e) (hg l j hl) (by norm_num : (0:ℝ)≤1/3)
  have h3:=Real.rpow_le_rpow (sixth_nonnegative f) (hg m n hm) (by norm_num : (0:ℝ)≤1/3)
  have hb:=mul_le_mul (mul_le_mul h1 h2 (Real.rpow_nonneg (sixth_nonnegative e) _)
    (Real.rpow_nonneg (mul_nonneg (by positivity) (mass_nonnegative p k)) _)) h3
    (Real.rpow_nonneg (sixth_nonnegative f) _)
    (mul_nonneg (Real.rpow_nonneg (mul_nonneg (by positivity) (mass_nonnegative p k)) _)
      (Real.rpow_nonneg (mul_nonneg (by positivity) (mass_nonnegative p l)) _))
  have hc : ((2500*M^4)^((1:ℝ)/3))^3=2500*M^4 := by
    rw [←Real.rpow_natCast,←Real.rpow_mul (by positivity : 0 ≤ 2500*M^4)]
    norm_num
  have hr : (2500*M^4*mass p k)^((1:ℝ)/3)*(2500*M^4*mass p l)^((1:ℝ)/3)*
      (2500*M^4*mass p m)^((1:ℝ)/3)=
      2500*M^4*(mass p k)^((1:ℝ)/3)*(mass p l)^((1:ℝ)/3)*(mass p m)^((1:ℝ)/3) := by
    rw [Real.mul_rpow (by positivity : 0 ≤ 2500*M^4) (mass_nonnegative p k),
      Real.mul_rpow (by positivity : 0 ≤ 2500*M^4) (mass_nonnegative p l),
      Real.mul_rpow (by positivity : 0 ≤ 2500*M^4) (mass_nonnegative p m)]
    calc
      _ =((2500*M^4)^((1:ℝ)/3))^3*(mass p k)^((1:ℝ)/3)*
        (mass p l)^((1:ℝ)/3)*(mass p m)^((1:ℝ)/3) := by ring
      _ =_ := by rw [hc]
  exact h.trans (hb.trans_eq hr)

end
end Resonance.SpatialProductGN
