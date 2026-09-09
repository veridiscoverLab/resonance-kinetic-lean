import Resonance.PhysicalCollisionForm
import Resonance.WeakCollision

/-! Construction of the original collision output in physical Lebesgue L².
The adjoint construction is identified against every physical L² test with the
original common-measure output row. Its directional derivative is proved in
the physical L² norm by an exact vector-valued cubic identity. -/
open MeasureTheory
open scoped ENNReal

namespace Resonance.PhysicalNonlinear
noncomputable section
open Collision CollisionLinearization ResonantMeasure PhysicalMarginal
open PhysicalCollisionForm WeakCollision

def leg {R : ℝ} (hR : 0 ≤ R) (i : Fin 4) : H R →L[ℝ] J R :=
  (CollisionForm.pullback R i).toContinuousLinearMap.comp (inclusionCLM hR)

theorem leg_ae {R : ℝ} (hR : 0 ≤ R) (i : Fin 4) (f : H R) :
    leg hR i f =ᵐ[pairingMeasure R] (fun k => f (k i)) := by
  have hi := (CollisionForm.all_legs_preserve R i).quasiMeasurePreserving.ae_eq
    (inclusion_ae hR f)
  exact (CollisionForm.pullback_ae R i (inclusion hR f)).trans hi

theorem leg_bound {R : ℝ} (hR : 0 ≤ R) (i : Fin 4) (f : H R) :
    ‖leg hR i f‖ ≤ inclusionNorm R * ‖f‖ := by
  change ‖CollisionForm.pullback R i (inclusion hR f)‖ ≤ _
  rw [(CollisionForm.pullback R i).norm_map]
  exact inclusion_bound hR f

theorem joint_polynomial_memLp {R : ℝ} (hR : 0 ≤ R) {f : E → ℝ}
    (hf : MemLp f ∞ (physicalMeasure R)) :
    MemLp (fun k : FourMomenta => collisionPolynomial (fun i => f (k i))) 2 (pairingMeasure R) := by
  letI := pairingMeasure_finite hR
  exact (polynomial_memLp_top (fun k : FourMomenta => fun i => f (k i))
    (fun i => cube_leg_memLp hR i hf)).mono_exponent (by simp)

theorem joint_linear_memLp {R : ℝ} (hR : 0 ≤ R) {f h : E → ℝ}
    (hf : MemLp f ∞ (physicalMeasure R)) (hh : MemLp h ∞ (physicalMeasure R)) :
    MemLp (fun k : FourMomenta => linearCoefficient (fun i => f (k i)) (fun i => h (k i)))
      2 (pairingMeasure R) := by
  letI := pairingMeasure_finite hR
  exact (linearCoefficient_memLp_top (fun k : FourMomenta => fun i => f (k i))
    (fun k : FourMomenta => fun i => h (k i))
    (fun i => cube_leg_memLp hR i hf) (fun i => cube_leg_memLp hR i hh)).mono_exponent (by simp)

def jointPolynomial {R : ℝ} (hR : 0 ≤ R) (f : E → ℝ)
    (hf : MemLp f ∞ (physicalMeasure R)) : J R :=
  (joint_polynomial_memLp hR hf).toLp _

def jointLinear {R : ℝ} (hR : 0 ≤ R) (f h : E → ℝ)
    (hf : MemLp f ∞ (physicalMeasure R)) (hh : MemLp h ∞ (physicalMeasure R)) : J R :=
  (joint_linear_memLp hR hf hh).toLp _

theorem jointPolynomial_ae {R : ℝ} (hR : 0 ≤ R) (f : E → ℝ)
    (hf : MemLp f ∞ (physicalMeasure R)) :
    jointPolynomial hR f hf =ᵐ[pairingMeasure R]
      (fun k => collisionPolynomial (fun i => f (k i))) := MemLp.coeFn_toLp _

theorem jointLinear_ae {R : ℝ} (hR : 0 ≤ R) (f h : E → ℝ)
    (hf : MemLp f ∞ (physicalMeasure R)) (hh : MemLp h ∞ (physicalMeasure R)) :
    jointLinear hR f h hf hh =ᵐ[pairingMeasure R]
      (fun k => linearCoefficient (fun i => f (k i)) (fun i => h (k i))) := MemLp.coeFn_toLp _

def output {R : ℝ} (hR : 0 ≤ R) (f : E → ℝ)
    (hf : MemLp f ∞ (physicalMeasure R)) : H R :=
  (leg hR 0).adjoint (jointPolynomial hR f hf)

def linearOutput {R : ℝ} (hR : 0 ≤ R) (f h : E → ℝ)
    (hf : MemLp f ∞ (physicalMeasure R)) (hh : MemLp h ∞ (physicalMeasure R)) : H R :=
  (leg hR 0).adjoint (jointLinear hR f h hf hh)

theorem original_row_integrable {R : ℝ} (hR : 0 ≤ R) {f : E → ℝ}
    (hf : MemLp f ∞ (physicalMeasure R)) (g : H R) :
    Integrable (originalDensity f g) (pairingMeasure R) :=
  (joint_polynomial_memLp hR hf).integrable_mul (cube_leg_memLp hR 0 (Lp.memLp g))

/-- This identifies the constructed output with the original row for every
physical L² test, not merely bounded tests or an abstract duality axiom. -/
theorem output_pairing {R : ℝ} (hR : 0 ≤ R) (f : E → ℝ)
    (hf : MemLp f ∞ (physicalMeasure R)) (g : H R) :
    inner ℝ g (output hR f hf) = ∫ k, originalDensity f g k ∂pairingMeasure R := by
  rw [output, ContinuousLinearMap.adjoint_inner_right, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [leg_ae hR 0 g, jointPolynomial_ae hR f hf] with k hg hf'
  rw [hg, hf']
  rfl

theorem linearOutput_pairing {R : ℝ} (hR : 0 ≤ R) (f h : E → ℝ)
    (hf : MemLp f ∞ (physicalMeasure R)) (hh : MemLp h ∞ (physicalMeasure R)) (g : H R) :
    inner ℝ g (linearOutput hR f h hf hh) =
      ∫ k, linearCoefficient (fun i => f (k i)) (fun i => h (k i)) * g (k 0)
        ∂pairingMeasure R := by
  rw [linearOutput, ContinuousLinearMap.adjoint_inner_right, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [leg_ae hR 0 g, jointLinear_ae hR f h hf hh] with k hg hf'
  rw [hg, hf']
  rfl

theorem output_unique {R : ℝ} (hR : 0 ≤ R) (f : E → ℝ)
    (hf : MemLp f ∞ (physicalMeasure R)) (Q : H R)
    (hQ : ∀ g : H R, inner ℝ g Q = ∫ k, originalDensity f g k ∂pairingMeasure R) :
    Q = output hR f hf :=
  ext_inner_left ℝ (fun g => (hQ g).trans (output_pairing hR f hf g).symm)

theorem jointPolynomial_exact_cubic {R : ℝ} (hR : 0 ≤ R) (f h : E → ℝ)
    (hf : MemLp f ∞ (physicalMeasure R)) (hh : MemLp h ∞ (physicalMeasure R)) (t : ℝ) :
    jointPolynomial hR (fun p => f p + t * h p) (hf.add (hh.const_mul t)) =
      jointPolynomial hR f hf + t • jointLinear hR f h hf hh +
      t ^ 2 • jointLinear hR h f hh hf + t ^ 3 • jointPolynomial hR h hh := by
  apply Lp.ext
  have ha := Lp.coeFn_add
    (jointPolynomial hR f hf + t • jointLinear hR f h hf hh + t ^ 2 • jointLinear hR h f hh hf)
    (t ^ 3 • jointPolynomial hR h hh)
  have hb := Lp.coeFn_add (jointPolynomial hR f hf + t • jointLinear hR f h hf hh)
    (t ^ 2 • jointLinear hR h f hh hf)
  have hc := Lp.coeFn_add (jointPolynomial hR f hf) (t • jointLinear hR f h hf hh)
  filter_upwards [jointPolynomial_ae hR (fun p => f p + t * h p) (hf.add (hh.const_mul t)),
    jointPolynomial_ae hR f hf, jointPolynomial_ae hR h hh,
    jointLinear_ae hR f h hf hh, jointLinear_ae hR h f hh hf, ha, hb, hc,
    Lp.coeFn_smul t (jointLinear hR f h hf hh),
    Lp.coeFn_smul (t ^ 2) (jointLinear hR h f hh hf),
    Lp.coeFn_smul (t ^ 3) (jointPolynomial hR h hh)] with k ht hf' hh' hl hl' ha hb hc hs hs' hs''
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at ha hb hc hs hs' hs''
  rw [ht, ha, hb, hc, hs, hs', hs'', hf', hh', hl, hl']
  exact collisionPolynomial_exact_cubic _ _ t

theorem output_exact_cubic {R : ℝ} (hR : 0 ≤ R) (f h : E → ℝ)
    (hf : MemLp f ∞ (physicalMeasure R)) (hh : MemLp h ∞ (physicalMeasure R)) (t : ℝ) :
    output hR (fun p => f p + t * h p) (hf.add (hh.const_mul t)) =
      output hR f hf + t • linearOutput hR f h hf hh +
      t ^ 2 • linearOutput hR h f hh hf + t ^ 3 • output hR h hh := by
  have he := congrArg (fun u : J R => (leg hR 0).adjoint u)
    (jointPolynomial_exact_cubic hR f h hf hh t)
  simpa only [map_add, map_smul, output, linearOutput] using he

theorem output_directional_derivative {R : ℝ} (hR : 0 ≤ R) (f h : E → ℝ)
    (hf : MemLp f ∞ (physicalMeasure R)) (hh : MemLp h ∞ (physicalMeasure R)) :
    HasDerivAt (fun t : ℝ => output hR (fun p => f p + t * h p) (hf.add (hh.const_mul t)))
      (linearOutput hR f h hf hh) 0 := by
  have he : (fun t : ℝ => output hR (fun p => f p + t * h p) (hf.add (hh.const_mul t))) =
      (fun t => output hR f hf + t • linearOutput hR f h hf hh +
        t ^ 2 • linearOutput hR h f hh hf + t ^ 3 • output hR h hh) :=
    funext (output_exact_cubic hR f h hf hh)
  rw [he]
  convert (((hasDerivAt_const (0 : ℝ) (output hR f hf)).add
    ((hasDerivAt_id 0).smul_const (linearOutput hR f h hf hh))).add
    (((hasDerivAt_id 0).pow 2).smul_const (linearOutput hR h f hh hf))).add
    (((hasDerivAt_id 0).pow 3).smul_const (output hR h hh)) using 1
  simp

end
end Resonance.PhysicalNonlinear
