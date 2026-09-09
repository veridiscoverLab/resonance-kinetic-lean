import Mathlib

/-!
Continuous-measure entropy geometry for Rayleigh--Jeans moment matching.
The real-valued integral theorems below carry explicit finite-entropy hypotheses;
no conclusion is inferred from the default value of a nonintegrable Bochner integral.
-/

open MeasureTheory
open scoped BigOperators ENNReal

namespace Resonance.Entropy

noncomputable def density (x y : ℝ) : ℝ := x / y - 1 - Real.log (x / y)

noncomputable def entropy {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (f g : α → ℝ) : ℝ := ∫ x, density (f x) (g x) ∂μ

theorem density_threepoint {x y z : ℝ} (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) :
    density x z = density x y + density y z + (x-y) * (z⁻¹-y⁻¹) := by
  unfold density
  rw [Real.log_div (ne_of_gt hx) (ne_of_gt hz),
    Real.log_div (ne_of_gt hx) (ne_of_gt hy),
    Real.log_div (ne_of_gt hy) (ne_of_gt hz)]
  field_simp
  ring

theorem density_nonneg {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    0 ≤ density x y := by
  exact sub_nonneg.mpr (Real.log_le_sub_one_of_pos (div_pos hx hy))

theorem density_eq_zero_iff {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    density x y = 0 ↔ x = y := by
  constructor
  · intro h
    by_contra hxy
    have hratio : x / y ≠ 1 := by
      intro hratio
      exact hxy ((div_eq_one_iff_eq (ne_of_gt hy)).mp hratio)
    have := Real.log_lt_sub_one_of_pos (div_pos hx hy) hratio
    unfold density at h
    linarith
  · rintro rfl
    simp [density, ne_of_gt hy]

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

theorem integral_threepoint {f g h : α → ℝ}
    (hf : ∀ᵐ x ∂μ, 0 < f x) (hg : ∀ᵐ x ∂μ, 0 < g x)
    (hh : ∀ᵐ x ∂μ, 0 < h x)
    (hfg : Integrable (fun x => density (f x) (g x)) μ)
    (hgh : Integrable (fun x => density (g x) (h x)) μ)
    (hcross : Integrable (fun x => (f x-g x) * ((h x)⁻¹-(g x)⁻¹)) μ) :
    entropy μ f h = entropy μ f g + entropy μ g h +
      ∫ x, (f x-g x) * ((h x)⁻¹-(g x)⁻¹) ∂μ := by
  unfold entropy
  calc
    _ = ∫ x, (density (f x) (g x) + density (g x) (h x)) +
        (f x-g x) * ((h x)⁻¹-(g x)⁻¹) ∂μ := by
      apply integral_congr_ae
      filter_upwards [hf, hg, hh] with x hfx hgx hhx
      exact density_threepoint hfx hgx hhx
    _ = _ := by
      rw [integral_add (f := fun x => density (f x) (g x) + density (g x) (h x))
        (g := fun x => (f x-g x) * ((h x)⁻¹-(g x)⁻¹)) (hfg.add hgh) hcross,
        integral_add hfg hgh]

noncomputable def denominator {n : ℕ} (ψ : Fin n → α → ℝ) (θ : Fin n → ℝ)
    (x : α) : ℝ := ∑ i, θ i * ψ i x

noncomputable def rj {n : ℕ} (ψ : Fin n → α → ℝ) (θ : Fin n → ℝ)
    (x : α) : ℝ := (denominator ψ θ x)⁻¹

noncomputable def moment {n : ℕ} (μ : Measure α) (ψ : Fin n → α → ℝ)
    (f : α → ℝ) (i : Fin n) : ℝ := ∫ x, ψ i x * f x ∂μ

omit [MeasurableSpace α] in
theorem mul_denominator {n : ℕ} (ψ : Fin n → α → ℝ) (θ : Fin n → ℝ)
    (f : α → ℝ) (x : α) :
    f x * denominator ψ θ x = ∑ i, θ i * (ψ i x * f x) := by
  simp only [denominator, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem integrable_mul_denominator {n : ℕ} (ψ : Fin n → α → ℝ)
    (θ : Fin n → ℝ) {f : α → ℝ}
    (hf : ∀ i, Integrable (fun x => ψ i x * f x) μ) :
    Integrable (fun x => f x * denominator ψ θ x) μ := by
  simp only [mul_denominator]
  exact integrable_finset_sum Finset.univ (fun i _ => (hf i).const_mul (θ i))

omit [MeasurableSpace α] in
theorem cross_expansion {n : ℕ} (ψ : Fin n → α → ℝ)
    (θ β : Fin n → ℝ) (f : α → ℝ) (x : α) :
    (f x-rj ψ θ x) * ((rj ψ β x)⁻¹-(rj ψ θ x)⁻¹) =
      ∑ i, (β i-θ i) * (ψ i x * f x - ψ i x * rj ψ θ x) := by
  simp only [rj, inv_inv, denominator, ← Finset.sum_sub_distrib]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem integrable_cross {n : ℕ} (ψ : Fin n → α → ℝ)
    (θ β : Fin n → ℝ) {f : α → ℝ}
    (hf : ∀ i, Integrable (fun x => ψ i x * f x) μ)
    (hN : ∀ i, Integrable (fun x => ψ i x * rj ψ θ x) μ) :
    Integrable (fun x => (f x-rj ψ θ x) *
      ((rj ψ β x)⁻¹-(rj ψ θ x)⁻¹)) μ := by
  simp only [cross_expansion]
  exact integrable_finset_sum Finset.univ
    (fun i _ => ((hf i).sub (hN i)).const_mul (β i-θ i))

theorem integral_cross {n : ℕ} (ψ : Fin n → α → ℝ)
    (θ β : Fin n → ℝ) {f : α → ℝ}
    (hf : ∀ i, Integrable (fun x => ψ i x * f x) μ)
    (hN : ∀ i, Integrable (fun x => ψ i x * rj ψ θ x) μ) :
    (∫ x, (f x-rj ψ θ x) * ((rj ψ β x)⁻¹-(rj ψ θ x)⁻¹) ∂μ) =
      ∑ i, (β i-θ i) * (moment μ ψ f i - moment μ ψ (rj ψ θ) i) := by
  simp only [cross_expansion]
  rw [integral_finset_sum (f := fun i x =>
      (β i-θ i) * (ψ i x * f x - ψ i x * rj ψ θ x)) Finset.univ
    (fun i _ => ((hf i).sub (hN i)).const_mul (β i-θ i))]
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_const_mul, integral_sub (hf i) (hN i)]
  rfl

theorem rj_threepoint {n : ℕ} (ψ : Fin n → α → ℝ)
    (θ β : Fin n → ℝ) {f : α → ℝ}
    (hfpos : ∀ᵐ x ∂μ, 0 < f x)
    (hθ : ∀ᵐ x ∂μ, 0 < denominator ψ θ x)
    (hβ : ∀ᵐ x ∂μ, 0 < denominator ψ β x)
    (hf : ∀ i, Integrable (fun x => ψ i x * f x) μ)
    (hN : ∀ i, Integrable (fun x => ψ i x * rj ψ θ x) μ)
    (hent : Integrable (fun x => density (f x) (rj ψ θ x)) μ)
    (hNN : Integrable (fun x => density (rj ψ θ x) (rj ψ β x)) μ) :
    entropy μ f (rj ψ β) = entropy μ f (rj ψ θ) +
      entropy μ (rj ψ θ) (rj ψ β) +
      ∑ i, (β i-θ i) * (moment μ ψ f i - moment μ ψ (rj ψ θ) i) := by
  have hNpos : ∀ᵐ x ∂μ, 0 < rj ψ θ x := by
    filter_upwards [hθ] with x hx
    exact inv_pos.mpr hx
  have hBpos : ∀ᵐ x ∂μ, 0 < rj ψ β x := by
    filter_upwards [hβ] with x hx
    exact inv_pos.mpr hx
  rw [integral_threepoint hfpos hNpos hBpos hent hNN (integrable_cross ψ θ β hf hN)]
  rw [integral_cross ψ θ β hf hN]

theorem rj_pythagoras {n : ℕ} (ψ : Fin n → α → ℝ)
    (θ β : Fin n → ℝ) {f : α → ℝ}
    (hfpos : ∀ᵐ x ∂μ, 0 < f x)
    (hθ : ∀ᵐ x ∂μ, 0 < denominator ψ θ x)
    (hβ : ∀ᵐ x ∂μ, 0 < denominator ψ β x)
    (hf : ∀ i, Integrable (fun x => ψ i x * f x) μ)
    (hN : ∀ i, Integrable (fun x => ψ i x * rj ψ θ x) μ)
    (hent : Integrable (fun x => density (f x) (rj ψ θ x)) μ)
    (hNN : Integrable (fun x => density (rj ψ θ x) (rj ψ β x)) μ)
    (hmatch : ∀ i, moment μ ψ f i = moment μ ψ (rj ψ θ) i) :
    entropy μ f (rj ψ β) = entropy μ f (rj ψ θ) +
      entropy μ (rj ψ θ) (rj ψ β) := by
  rw [rj_threepoint ψ θ β hfpos hθ hβ hf hN hent hNN]
  simp [hmatch]


theorem integrable_density [IsFiniteMeasure μ] {f g : α → ℝ}
    (hfpos : ∀ᵐ x ∂μ, 0 < f x) (hgpos : ∀ᵐ x ∂μ, 0 < g x)
    (hquot : Integrable (fun x => f x / g x) μ)
    (hf : Integrable (fun x => Real.log (f x)) μ)
    (hg : Integrable (fun x => Real.log (g x)) μ) :
    Integrable (fun x => density (f x) (g x)) μ := by
  have hh : Integrable (fun x => (f x / g x - 1) -
      (Real.log (f x) - Real.log (g x))) μ :=
    (hquot.sub (integrable_const 1)).sub (hf.sub hg)
  apply hh.congr
  filter_upwards [hfpos, hgpos] with x hfx hgx
  simp only [density, Real.log_div (ne_of_gt hfx) (ne_of_gt hgx)]

/-- The continuous integral three-point formula, with all entropy integrability
derived from moment-product integrability and logarithmic integrability. -/
theorem rj_threepoint_of_log_integrable [IsFiniteMeasure μ] {n : ℕ}
    (ψ : Fin n → α → ℝ) (θ β : Fin n → ℝ) {f : α → ℝ}
    (hfpos : ∀ᵐ x ∂μ, 0 < f x)
    (hθ : ∀ᵐ x ∂μ, 0 < denominator ψ θ x)
    (hβ : ∀ᵐ x ∂μ, 0 < denominator ψ β x)
    (hf : ∀ i, Integrable (fun x => ψ i x * f x) μ)
    (hN : ∀ i, Integrable (fun x => ψ i x * rj ψ θ x) μ)
    (hlogf : Integrable (fun x => Real.log (f x)) μ)
    (hlogN : Integrable (fun x => Real.log (rj ψ θ x)) μ)
    (hlogB : Integrable (fun x => Real.log (rj ψ β x)) μ) :
    entropy μ f (rj ψ β) = entropy μ f (rj ψ θ) +
      entropy μ (rj ψ θ) (rj ψ β) +
      ∑ i, (β i-θ i) * (moment μ ψ f i - moment μ ψ (rj ψ θ) i) := by
  have hNpos : ∀ᵐ x ∂μ, 0 < rj ψ θ x := by
    filter_upwards [hθ] with x hx
    exact inv_pos.mpr hx
  have hBpos : ∀ᵐ x ∂μ, 0 < rj ψ β x := by
    filter_upwards [hβ] with x hx
    exact inv_pos.mpr hx
  have hfquot : Integrable (fun x => f x / rj ψ θ x) μ := by
    simpa only [rj, div_inv_eq_mul] using integrable_mul_denominator ψ θ hf
  have hNquot : Integrable (fun x => rj ψ θ x / rj ψ β x) μ := by
    simpa only [rj, div_inv_eq_mul] using integrable_mul_denominator ψ β hN
  exact rj_threepoint ψ θ β hfpos hθ hβ hf hN
    (integrable_density hfpos hNpos hfquot hlogf hlogN)
    (integrable_density hNpos hBpos hNquot hlogN hlogB)

theorem rj_pythagoras_of_log_integrable [IsFiniteMeasure μ] {n : ℕ}
    (ψ : Fin n → α → ℝ) (θ β : Fin n → ℝ) {f : α → ℝ}
    (hfpos : ∀ᵐ x ∂μ, 0 < f x)
    (hθ : ∀ᵐ x ∂μ, 0 < denominator ψ θ x)
    (hβ : ∀ᵐ x ∂μ, 0 < denominator ψ β x)
    (hf : ∀ i, Integrable (fun x => ψ i x * f x) μ)
    (hN : ∀ i, Integrable (fun x => ψ i x * rj ψ θ x) μ)
    (hlogf : Integrable (fun x => Real.log (f x)) μ)
    (hlogN : Integrable (fun x => Real.log (rj ψ θ x)) μ)
    (hlogB : Integrable (fun x => Real.log (rj ψ β x)) μ)
    (hmatch : ∀ i, moment μ ψ f i = moment μ ψ (rj ψ θ) i) :
    entropy μ f (rj ψ β) = entropy μ f (rj ψ θ) +
      entropy μ (rj ψ θ) (rj ψ β) := by
  rw [rj_threepoint_of_log_integrable ψ θ β hfpos hθ hβ hf hN hlogf hlogN hlogB]
  simp [hmatch]

/-- Nonnegativity of the totalized Bochner integral. For the manuscript's
potentially infinite entropy use `extendedEntropy`; its finite-value bridge is
`extendedEntropy_eq_ofReal_entropy`. -/
theorem entropy_nonneg {f g : α → ℝ}
    (hf : ∀ᵐ x ∂μ, 0 < f x) (hg : ∀ᵐ x ∂μ, 0 < g x) :
    0 ≤ entropy μ f g := by
  apply integral_nonneg_of_ae
  filter_upwards [hf, hg] with x hfx hgx
  exact density_nonneg hfx hgx

theorem entropy_eq_zero_iff {f g : α → ℝ}
    (hf : ∀ᵐ x ∂μ, 0 < f x) (hg : ∀ᵐ x ∂μ, 0 < g x)
    (hint : Integrable (fun x => density (f x) (g x)) μ) :
    entropy μ f g = 0 ↔ f =ᵐ[μ] g := by
  have hn : ∀ᵐ x ∂μ, 0 ≤ density (f x) (g x) := by
    filter_upwards [hf, hg] with x hfx hgx
    exact density_nonneg hfx hgx
  rw [entropy, integral_eq_zero_iff_of_nonneg_ae hn hint]
  constructor
  · intro he
    filter_upwards [hf, hg, he] with x hfx hgx hex
    exact (density_eq_zero_iff hfx hgx).mp hex
  · intro he
    filter_upwards [hf, hg, he] with x hfx hgx hex
    exact (density_eq_zero_iff hfx hgx).mpr hex



/-- Nonnegative entropy with its genuine extended-real value, including infinity. -/
noncomputable def extendedEntropy (μ : Measure α) (f g : α → ℝ) : ℝ≥0∞ :=
  ∫⁻ x, ENNReal.ofReal (density (f x) (g x)) ∂μ

/-- Adding an integrable, zero-mean signed perturbation preserves the integral
of a nonnegative function, even when that integral is infinite. -/
theorem lintegral_eq_of_zero_mean_perturbation {a b p : α → ℝ}
    (ha : ∀ᵐ x ∂μ, 0 ≤ a x) (hb : ∀ᵐ x ∂μ, 0 ≤ b x)
    (hp : Integrable p μ) (hpzero : ∫ x, p x ∂μ = 0)
    (he : ∀ᵐ x ∂μ, a x = b x + p x) :
    (∫⁻ x, ENNReal.ofReal (a x) ∂μ) = ∫⁻ x, ENNReal.ofReal (b x) ∂μ := by
  let pp := fun x => max (p x) 0
  let pn := fun x => max (-p x) 0
  have hpp : Integrable pp μ := hp.pos_part
  have hpn : Integrable pn μ := hp.neg.pos_part
  have hpp0 : ∀ x, 0 ≤ pp x := fun x => le_max_right _ _
  have hpn0 : ∀ x, 0 ≤ pn x := fun x => le_max_right _ _
  have hdiff : ∀ x, pp x - pn x = p x := by
    intro x
    dsimp [pp, pn]
    by_cases hx : 0 ≤ p x
    · rw [max_eq_left hx, max_eq_right (neg_nonpos.mpr hx)]
      ring
    · have hx' : p x ≤ 0 := le_of_not_ge hx
      rw [max_eq_right hx', max_eq_left (neg_nonneg.mpr hx')]
      ring
  have hreal : (∫ x, pp x ∂μ) = ∫ x, pn x ∂μ := by
    apply sub_eq_zero.mp
    rw [← integral_sub hpp hpn]
    calc
      _ = ∫ x, p x ∂μ := integral_congr_ae (Filter.Eventually.of_forall hdiff)
      _ = 0 := hpzero
  have hposneg : (∫⁻ x, ENNReal.ofReal (pp x) ∂μ) =
      ∫⁻ x, ENNReal.ofReal (pn x) ∂μ := by
    rw [← ofReal_integral_eq_lintegral_ofReal hpp (Filter.Eventually.of_forall hpp0),
      ← ofReal_integral_eq_lintegral_ofReal hpn (Filter.Eventually.of_forall hpn0),
      hreal]
  have hnfinite : (∫⁻ x, ENNReal.ofReal (pn x) ∂μ) ≠ ⊤ :=
    ne_of_lt ((hasFiniteIntegral_iff_ofReal
      (Filter.Eventually.of_forall hpn0)).mp hpn.hasFiniteIntegral)
  have heq :
      (∫⁻ x, ENNReal.ofReal (pn x) ∂μ) + (∫⁻ x, ENNReal.ofReal (a x) ∂μ) =
      (∫⁻ x, ENNReal.ofReal (pp x) ∂μ) + (∫⁻ x, ENNReal.ofReal (b x) ∂μ) := by
    rw [← lintegral_add_left' hpn.aestronglyMeasurable.aemeasurable.ennreal_ofReal,
      ← lintegral_add_left' hpp.aestronglyMeasurable.aemeasurable.ennreal_ofReal]
    apply lintegral_congr_ae
    filter_upwards [ha, hb, he] with x hax hbx hex
    rw [← ENNReal.ofReal_add (hpn0 x) hax, ← ENNReal.ofReal_add (hpp0 x) hbx]
    congr 1
    have hd := hdiff x
    linarith
  rw [hposneg] at heq
  exact (ENNReal.add_right_inj hnfinite).mp heq

theorem aemeasurable_density {f g : α → ℝ}
    (hf : AEMeasurable f μ) (hg : AEMeasurable g μ) :
    AEMeasurable (fun x => density (f x) (g x)) μ := by
  exact ((hf.div hg).sub aemeasurable_const).sub (hf.div hg).log

theorem aemeasurable_denominator {n : ℕ} {ψ : Fin n → α → ℝ}
    (hψ : ∀ i, AEMeasurable (ψ i) μ) (θ : Fin n → ℝ) :
    AEMeasurable (denominator ψ θ) μ := by
  have he : denominator ψ θ = ∑ i, (fun x => θ i * ψ i x) := by
    funext x
    simp [denominator]
  rw [he]
  exact Finset.aemeasurable_sum Finset.univ (fun i _ => (hψ i).const_mul (θ i))

/-- The full extended entropy Pythagorean identity: no entropy integrability
or finiteness hypothesis occurs. All cancellations come from the same moments. -/
theorem rj_pythagoras_extended {n : ℕ} (ψ : Fin n → α → ℝ)
    (θ β : Fin n → ℝ) {f : α → ℝ}
    (hfm : AEMeasurable f μ) (hψ : ∀ i, AEMeasurable (ψ i) μ)
    (hfpos : ∀ᵐ x ∂μ, 0 < f x)
    (hθ : ∀ᵐ x ∂μ, 0 < denominator ψ θ x)
    (hβ : ∀ᵐ x ∂μ, 0 < denominator ψ β x)
    (hf : ∀ i, Integrable (fun x => ψ i x * f x) μ)
    (hN : ∀ i, Integrable (fun x => ψ i x * rj ψ θ x) μ)
    (hmatch : ∀ i, moment μ ψ f i = moment μ ψ (rj ψ θ) i) :
    extendedEntropy μ f (rj ψ β) = extendedEntropy μ f (rj ψ θ) +
      extendedEntropy μ (rj ψ θ) (rj ψ β) := by
  have hNpos : ∀ᵐ x ∂μ, 0 < rj ψ θ x := by
    filter_upwards [hθ] with x hx
    exact inv_pos.mpr hx
  have hBpos : ∀ᵐ x ∂μ, 0 < rj ψ β x := by
    filter_upwards [hβ] with x hx
    exact inv_pos.mpr hx
  have hfg : ∀ᵐ x ∂μ, 0 ≤ density (f x) (rj ψ θ x) := by
    filter_upwards [hfpos, hNpos] with x hfx hnx
    exact density_nonneg hfx hnx
  have hgh : ∀ᵐ x ∂μ, 0 ≤ density (rj ψ θ x) (rj ψ β x) := by
    filter_upwards [hNpos, hBpos] with x hnx hbx
    exact density_nonneg hnx hbx
  have hfh : ∀ᵐ x ∂μ, 0 ≤ density (f x) (rj ψ β x) := by
    filter_upwards [hfpos, hBpos] with x hfx hbx
    exact density_nonneg hfx hbx
  have hcross := integrable_cross ψ θ β hf hN
  have hzero : (∫ x, (f x-rj ψ θ x) *
      ((rj ψ β x)⁻¹-(rj ψ θ x)⁻¹) ∂μ) = 0 := by
    rw [integral_cross ψ θ β hf hN]
    simp [hmatch]
  have hpert : ∀ᵐ x ∂μ, density (f x) (rj ψ β x) =
      (density (f x) (rj ψ θ x) + density (rj ψ θ x) (rj ψ β x)) +
      (f x-rj ψ θ x) * ((rj ψ β x)⁻¹-(rj ψ θ x)⁻¹) := by
    filter_upwards [hfpos, hNpos, hBpos] with x hfx hnx hbx
    exact density_threepoint hfx hnx hbx
  unfold extendedEntropy
  calc
    _ = ∫⁻ x, ENNReal.ofReal
        (density (f x) (rj ψ θ x) + density (rj ψ θ x) (rj ψ β x)) ∂μ :=
      lintegral_eq_of_zero_mean_perturbation hfh
        (by filter_upwards [hfg, hgh] with x hx hy; exact add_nonneg hx hy)
        hcross hzero hpert
    _ = ∫⁻ x, ENNReal.ofReal (density (f x) (rj ψ θ x)) +
        ENNReal.ofReal (density (rj ψ θ x) (rj ψ β x)) ∂μ := by
      apply lintegral_congr_ae
      filter_upwards [hfg, hgh] with x hx hy
      exact ENNReal.ofReal_add hx hy
    _ = _ := lintegral_add_left'
      (aemeasurable_density hfm (aemeasurable_denominator hψ θ).inv).ennreal_ofReal _



/-! The actual three-dimensional sharp cube and its five moment functions. -/

def sharpCube (R : ℝ) : Set (Fin 3 → ℝ) :=
  Set.Icc (fun _ => -R) (fun _ => R)

noncomputable def cubeMeasure (R : ℝ) : Measure (Fin 3 → ℝ) :=
  volume.restrict (sharpCube R)

def fiveInvariants (i : Fin 5) (k : Fin 3 → ℝ) : ℝ :=
  ![1, k 0, k 1, k 2, ∑ j : Fin 3, (k j)^2] i

theorem fiveInvariants_continuous (i : Fin 5) : Continuous (fiveInvariants i) := by
  change Continuous (fun k : Fin 3 → ℝ => ![1, k 0, k 1, k 2, ∑ j : Fin 3, (k j)^2] i)
  fin_cases i <;> dsimp <;> fun_prop

theorem cube_denominator_continuous (θ : Fin 5 → ℝ) :
    Continuous (denominator fiveInvariants θ) := by
  exact continuous_finset_sum Finset.univ
    (fun i _ => continuous_const.mul (fiveInvariants_continuous i))

theorem cube_rj_continuousOn (R : ℝ) (θ : Fin 5 → ℝ)
    (hθ : ∀ k ∈ sharpCube R, 0 < denominator fiveInvariants θ k) :
    ContinuousOn (rj fiveInvariants θ) (sharpCube R) :=
  (cube_denominator_continuous θ).continuousOn.inv₀ (fun k hk => ne_of_gt (hθ k hk))

theorem cube_finite (R : ℝ) : IsFiniteMeasure (cubeMeasure R) := by
  apply isFiniteMeasure_restrict.mpr
  exact ne_of_lt (isCompact_Icc.measure_lt_top)

theorem cube_denominator_pos_ae (R : ℝ) (θ : Fin 5 → ℝ)
    (hθ : ∀ k ∈ sharpCube R, 0 < denominator fiveInvariants θ k) :
    ∀ᵐ k ∂cubeMeasure R, 0 < denominator fiveInvariants θ k := by
  filter_upwards [ae_restrict_mem (μ := volume)
    (s := sharpCube R) measurableSet_Icc] with k hk
  exact hθ k hk

theorem cube_moment_integrable (R : ℝ) {f : (Fin 3 → ℝ) → ℝ}
    (hf : Integrable f (cubeMeasure R)) (i : Fin 5) :
    Integrable (fun k => fiveInvariants i k * f k) (cubeMeasure R) := by
  have hfon : IntegrableOn f (sharpCube R) volume := hf
  have ht := hfon.mul_continuousOn
    (fiveInvariants_continuous i).continuousOn isCompact_Icc
  simpa only [mul_comm] using ht

theorem cube_rj_moment_integrable (R : ℝ) (θ : Fin 5 → ℝ)
    (hθ : ∀ k ∈ sharpCube R, 0 < denominator fiveInvariants θ k) (i : Fin 5) :
    Integrable (fun k => fiveInvariants i k * rj fiveInvariants θ k)
      (cubeMeasure R) :=
  ((fiveInvariants_continuous i).continuousOn.mul
    (cube_rj_continuousOn R θ hθ)).integrableOn_Icc

theorem cube_rj_log_integrable (R : ℝ) (θ : Fin 5 → ℝ)
    (hθ : ∀ k ∈ sharpCube R, 0 < denominator fiveInvariants θ k) :
    Integrable (fun k => Real.log (rj fiveInvariants θ k)) (cubeMeasure R) :=
  ((cube_rj_continuousOn R θ hθ).log
    (fun k hk => inv_ne_zero (ne_of_gt (hθ k hk)))).integrableOn_Icc

/-- The manuscript's finite-entropy three-point identity on the original cube.
The moment and RJ logarithm integrability conditions have been proved above,
rather than required as additional hypotheses. -/
theorem cube_entropy_threepoint (R : ℝ) (θ β : Fin 5 → ℝ)
    {f : (Fin 3 → ℝ) → ℝ}
    (hθ : ∀ k ∈ sharpCube R, 0 < denominator fiveInvariants θ k)
    (hβ : ∀ k ∈ sharpCube R, 0 < denominator fiveInvariants β k)
    (hfpos : ∀ᵐ k ∂cubeMeasure R, 0 < f k)
    (hf : Integrable f (cubeMeasure R))
    (hlogf : Integrable (fun k => Real.log (f k)) (cubeMeasure R)) :
    entropy (cubeMeasure R) f (rj fiveInvariants β) =
      entropy (cubeMeasure R) f (rj fiveInvariants θ) +
      entropy (cubeMeasure R) (rj fiveInvariants θ) (rj fiveInvariants β) +
      ∑ i : Fin 5, (β i-θ i) * (moment (cubeMeasure R) fiveInvariants f i -
        moment (cubeMeasure R) fiveInvariants (rj fiveInvariants θ) i) := by
  letI := cube_finite R
  exact rj_threepoint_of_log_integrable fiveInvariants θ β hfpos
    (cube_denominator_pos_ae R θ hθ) (cube_denominator_pos_ae R β hβ)
    (cube_moment_integrable R hf) (cube_rj_moment_integrable R θ hθ)
    hlogf (cube_rj_log_integrable R θ hθ) (cube_rj_log_integrable R β hβ)

/-- Five actual moments imply the cube Pythagorean identity for finite entropy. -/
theorem cube_entropy_pythagoras (R : ℝ) (θ β : Fin 5 → ℝ)
    {f : (Fin 3 → ℝ) → ℝ}
    (hθ : ∀ k ∈ sharpCube R, 0 < denominator fiveInvariants θ k)
    (hβ : ∀ k ∈ sharpCube R, 0 < denominator fiveInvariants β k)
    (hfpos : ∀ᵐ k ∂cubeMeasure R, 0 < f k)
    (hf : Integrable f (cubeMeasure R))
    (hlogf : Integrable (fun k => Real.log (f k)) (cubeMeasure R))
    (hmatch : ∀ i : Fin 5, moment (cubeMeasure R) fiveInvariants f i =
      moment (cubeMeasure R) fiveInvariants (rj fiveInvariants θ) i) :
    entropy (cubeMeasure R) f (rj fiveInvariants β) =
      entropy (cubeMeasure R) f (rj fiveInvariants θ) +
      entropy (cubeMeasure R) (rj fiveInvariants θ) (rj fiveInvariants β) := by
  rw [cube_entropy_threepoint R θ β hθ hβ hfpos hf hlogf]
  simp [hmatch]

/-- The same original cube theorem with genuine extended entropy.
No logarithmic integrability hypothesis is imposed, so infinite entropy is covered. -/
theorem cube_entropy_pythagoras_extended (R : ℝ) (θ β : Fin 5 → ℝ)
    {f : (Fin 3 → ℝ) → ℝ}
    (hθ : ∀ k ∈ sharpCube R, 0 < denominator fiveInvariants θ k)
    (hβ : ∀ k ∈ sharpCube R, 0 < denominator fiveInvariants β k)
    (hfpos : ∀ᵐ k ∂cubeMeasure R, 0 < f k)
    (hf : Integrable f (cubeMeasure R))
    (hmatch : ∀ i : Fin 5, moment (cubeMeasure R) fiveInvariants f i =
      moment (cubeMeasure R) fiveInvariants (rj fiveInvariants θ) i) :
    extendedEntropy (cubeMeasure R) f (rj fiveInvariants β) =
      extendedEntropy (cubeMeasure R) f (rj fiveInvariants θ) +
      extendedEntropy (cubeMeasure R) (rj fiveInvariants θ) (rj fiveInvariants β) := by
  exact rj_pythagoras_extended fiveInvariants θ β hf.aestronglyMeasurable.aemeasurable
    (fun i => (fiveInvariants_continuous i).measurable.aemeasurable) hfpos
    (cube_denominator_pos_ae R θ hθ) (cube_denominator_pos_ae R β hβ)
    (cube_moment_integrable R hf) (cube_rj_moment_integrable R θ hθ) hmatch



/-- The two entropy definitions agree whenever the nonnegative density is
integrable. Outside this domain the extended definition, not the totalized
Bochner integral, represents the manuscript's entropy. -/
theorem extendedEntropy_eq_ofReal_entropy {f g : α → ℝ}
    (hf : ∀ᵐ x ∂μ, 0 < f x) (hg : ∀ᵐ x ∂μ, 0 < g x)
    (hint : Integrable (fun x => density (f x) (g x)) μ) :
    extendedEntropy μ f g = ENNReal.ofReal (entropy μ f g) := by
  unfold extendedEntropy entropy
  symm
  apply ofReal_integral_eq_lintegral_ofReal hint
  filter_upwards [hf, hg] with x hfx hgx
  exact density_nonneg hfx hgx


end Resonance.Entropy
