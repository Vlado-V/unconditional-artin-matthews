module

public import ArtinMatthews.SourceAdditiveMellinNormalized
public import Mathlib.Analysis.SpecialFunctions.Pow.Complex
public import Mathlib.Algebra.Order.Field.Pointwise


set_option backward.privateInPublic true
@[expose] public section

/-! Exact changes of scale for the additive and Mellin frequencies. The
Mellin phase is the literal complex power in Poisson–Dirichlet Lemma 6.4. -/

namespace ArtinMatthews
open MeasureTheory Set Filter
open scoped Pointwise BigOperators
noncomputable section

local notation "e" => OAI.Problem337.RealPhase.phase

def sourceLocalMellinPolynomial {ι : Type*} (S : Finset ι) (x : ι → ℝ) (a : ι → ℂ)
    (t : ℝ) : ℂ := ∑ i ∈ S, a i * (x i : ℂ) ^ (Complex.I * (t : ℂ))

def sourceLocalMellinEnergyDensity {ι : Type*} (S : Finset ι) (x : ι → ℝ) (a : ι → ℂ)
    (Y H : ℝ) (j : ℕ) (t : ℝ) : ℝ :=
  ((1 + H * |t| / Y) ^ j)⁻¹ * ‖sourceLocalMellinPolynomial S x a t‖ ^ 2

theorem sourceLocalMellinEnergyDensity_nonneg {ι : Type*} (S : Finset ι) (x : ι → ℝ)
    (a : ι → ℂ) {Y H : ℝ} (hY : 0 < Y) (hH : 0 < H) (j : ℕ) (t : ℝ) :
    0 ≤ sourceLocalMellinEnergyDensity S x a Y H j t := by
  unfold sourceLocalMellinEnergyDensity
  positivity

private theorem density_eq_weight {ι : Type*} (S : Finset ι) (x : ι → ℝ) (a : ι → ℂ)
    {Y H : ℝ} (hY : 0 < Y) (hH : 0 < H) (j : ℕ) (t : ℝ) :
    sourceLocalMellinEnergyDensity S x a Y H j t =
      markedMajorFourierWeight (Y / H) j t * ‖sourceLocalMellinPolynomial S x a t‖ ^ 2 := by
  unfold sourceLocalMellinEnergyDensity markedMajorFourierWeight
  rw [show |t| / (Y / H) = H * |t| / Y by field_simp [hY.ne', hH.ne']]

private theorem log_phase_eq_cpow {x : ℝ} (hx : 0 < x) (ξ : ℝ) :
    e (ξ * Real.log x) = (x : ℂ) ^ (Complex.I * ((2 * Real.pi * ξ : ℝ) : ℂ)) := by
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hx.ne'), ← Complex.ofReal_log hx.le]
  unfold OAI.Problem337.RealPhase.phase
  congr 1
  push_cast
  ring

private theorem mellin_log_norm {ι : Type*} (S : Finset ι) (x : ι → ℝ) (a : ι → ℂ)
    {Y : ℝ} (hY : 0 < Y) (hx : ∀ i ∈ S, 0 < x i) (ξ : ℝ) :
    ‖sourceLocalAdditivePolynomial S (fun i => Real.log (x i / Y)) a ξ‖ =
      ‖sourceLocalMellinPolynomial S x a (2 * Real.pi * ξ)‖ := by
  have he : sourceLocalAdditivePolynomial S (fun i => Real.log (x i / Y)) a ξ =
      e (-(ξ * Real.log Y)) * sourceLocalMellinPolynomial S x a (2 * Real.pi * ξ) := by
    unfold sourceLocalAdditivePolynomial sourceLocalMellinPolynomial
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    change a i * e (ξ * Real.log (x i / Y)) = _
    rw [Real.log_div (hx i hi).ne' hY.ne', mul_sub, sub_eq_add_neg,
      OAI.Problem337.RealPhase.phase_add, log_phase_eq_cpow (hx i hi)]
    ring
  rw [he, norm_mul, OAI.Problem337.RealPhase.norm_phase, one_mul]

theorem sourceLocalMellinEnergy_scale {ι : Type*} (S : Finset ι) (x : ι → ℝ) (a : ι → ℂ)
    {Y H : ℝ} (hY : 0 < Y) (hH : 0 < H) (hx : ∀ i ∈ S, 0 < x i)
    {j : ℕ} (hj : 2 ≤ j) :
    Integrable (sourceLocalMellinEnergyDensity S x a Y H j) ∧
    (∫ ξ : ℝ, markedMajorFourierWeight ((Y / H) / (2 * Real.pi)) j ξ *
        ‖sourceLocalAdditivePolynomial S (fun i => Real.log (x i / Y)) a ξ‖ ^ 2) =
      (2 * Real.pi)⁻¹ * ∫ t : ℝ, sourceLocalMellinEnergyDensity S x a Y H j t := by
  let T := Y / H
  let W := T / (2 * Real.pi)
  have hT : 0 < T := div_pos hY hH
  have hπ : 0 < 2 * Real.pi := by positivity
  have hW : 0 < W := div_pos hT hπ
  let m := sourceLocalMellinEnergyDensity S x a Y H j
  have he (ξ : ℝ) : m (2 * Real.pi * ξ) = markedMajorFourierWeight W j ξ *
      ‖sourceLocalAdditivePolynomial S (fun i => Real.log (x i / Y)) a ξ‖ ^ 2 := by
    dsimp only [m]
    rw [density_eq_weight S x a hY hH, mellin_log_norm S x a hY hx]
    unfold markedMajorFourierWeight
    rw [abs_mul, abs_of_pos hπ]
    have hs : |ξ| / W = (2 * Real.pi * |ξ|) / T := by
      dsimp only [W]
      field_simp [hT.ne', Real.pi_ne_zero]
    rw [hs]
  have hm : Integrable (fun ξ : ℝ => m (2 * Real.pi * ξ)) := by
    simpa only [he] using sourceLocalAdditivePolynomial_weight_integrable S
      (fun i => Real.log (x i / Y)) a hW hj
  refine ⟨(integrable_comp_mul_left_iff m hπ.ne').mp hm, ?_⟩
  change (∫ ξ : ℝ, markedMajorFourierWeight W j ξ *
    ‖sourceLocalAdditivePolynomial S (fun i => Real.log (x i / Y)) a ξ‖ ^ 2) = _
  simp_rw [← he]
  rw [Measure.integral_comp_mul_left, abs_of_nonneg (inv_nonneg.mpr hπ.le), smul_eq_mul]

theorem sourceLocalAdditiveEnergy_scale {ι : Type*} (S : Finset ι) (x : ι → ℝ) (a : ι → ℂ)
    {Y H : ℝ} (hY : 0 < Y) :
    (∫ β in Icc (-H⁻¹) H⁻¹, ‖sourceLocalAdditivePolynomial S x a β‖ ^ 2) =
      Y⁻¹ * ∫ β in Icc (-(Y / H)) (Y / H),
        ‖sourceLocalAdditivePolynomial S (fun i => x i / Y) a β‖ ^ 2 := by
  let f (β : ℝ) := ‖sourceLocalAdditivePolynomial S (fun i => x i / Y) a β‖ ^ 2
  have hf (β : ℝ) : f (Y • β) = ‖sourceLocalAdditivePolynomial S x a β‖ ^ 2 := by
    dsimp only [f, smul_eq_mul]
    congr 2
    unfold sourceLocalAdditivePolynomial
    apply Finset.sum_congr rfl
    intro i _
    congr 2
    field_simp [hY.ne']
  have h := Measure.setIntegral_comp_smul_of_pos (volume : Measure ℝ) f (Icc (-H⁻¹) H⁻¹) hY
  simp_rw [hf] at h
  simpa only [Module.finrank_self, pow_one, smul_eq_mul,
    LinearOrderedField.smul_Icc hY, mul_neg, ← div_eq_mul_inv, f] using h

/-- A stronger real-valued form of PD 6.4, with no diagonal error.
For `j ≥ 2` the literal weighted Mellin energy is integrable. -/
theorem sourceAdditiveMellinEnergy_real
    (c C : ℝ) (hc : 0 < c) (hcC : c ≤ C) (j : ℕ) (hj : 2 ≤ j) :
    ∃ K > 0, ∀ {ι : Type*} (S : Finset ι) (x : ι → ℝ) (a : ι → ℂ)
      (Y H : ℝ), 0 < Y → 0 < H → H ≤ Y → (∀ i ∈ S, x i ∈ Icc (c * Y) (C * Y)) →
      (∫ β in Icc (-H⁻¹) H⁻¹, ‖sourceLocalAdditivePolynomial S x a β‖ ^ 2) ≤
        K * (Y⁻¹ * ∫ t : ℝ, sourceLocalMellinEnergyDensity S x a Y H j t) := by
  obtain ⟨K, hK, h⟩ := sourceAdditiveMellinEnergy_normalized c C hc hcC j hj
  refine ⟨K / (2 * Real.pi), by positivity, ?_⟩
  intro ι S x a Y H hY hH hHY hx
  have hpos (i : ι) (hi : i ∈ S) : 0 < x i := (mul_pos hc hY).trans_le (hx i hi).1
  have hx' (i : ι) (hi : i ∈ S) : x i / Y ∈ Icc c C :=
    ⟨(le_div_iff₀ hY).2 (hx i hi).1, (div_le_iff₀ hY).2 (hx i hi).2⟩
  have hT : 1 ≤ Y / H := (le_div_iff₀ hH).2 (by simpa only [one_mul] using hHY)
  rw [sourceLocalAdditiveEnergy_scale S x a hY]
  calc
    _ ≤ Y⁻¹ * (K * ∫ t : ℝ, markedMajorFourierWeight ((Y / H) / (2 * Real.pi)) j t *
      ‖sourceLocalAdditivePolynomial S (fun i => Real.log (x i / Y)) a t‖ ^ 2) :=
        mul_le_mul_of_nonneg_left (h S (fun i => x i / Y) a hx' (Y / H) hT) (inv_nonneg.mpr hY.le)
    _ = _ := by
      rw [(sourceLocalMellinEnergy_scale S x a hY hH hpos hj).2]
      ring

end
end ArtinMatthews
