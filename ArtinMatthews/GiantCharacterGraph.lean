module

public import Mathlib.Analysis.Fourier.ZMod
public import Mathlib.NumberTheory.DirichletCharacter.Bounds
public import Mathlib.NumberTheory.MulChar.Lemmas
public import Mathlib.Tactic


set_option backward.privateInPublic true
@[expose] public section

/-! Finite character transport for the ordinary giant-factor graph argument.
The exact conjugations, nonunit values and endpoint phases are retained.
The elementary coefficient bound gives a fixed cost M, sufficient for any
logarithmic saving at a fixed modulus. -/
namespace ArtinMatthews
noncomputable section
open scoped BigOperators ComplexConjugate

theorem giant_character_shared_factor {M : ℕ} (χ : DirichletCharacter ℂ M)
    (r d y : ℕ) (hr : r.Coprime M) :
    conj (χ (r*d)) * χ (r*y) = conj (χ d) * χ y := by
  have hn : ‖χ (r : ZMod M)‖ = 1 := by
    simpa only [ZMod.coe_unitOfCoprime] using χ.unit_norm_eq_one (ZMod.unitOfCoprime r hr)
  have hc : conj (χ (r : ZMod M)) * χ r = 1 := by
    rw [← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq, hn]
    norm_num
  simp only [map_mul]
  calc
    _ = (conj (χ r) * χ r) * (conj (χ d) * χ y) := by ring
    _ = _ := by rw [hc, one_mul]

def giantCharacterAdditiveCoefficient {M : ℕ} [NeZero M]
    (χ : DirichletCharacter ℂ M) (r : ZMod M) : ℂ :=
  (M : ℂ)⁻¹ * ZMod.dft (fun a : ZMod M => χ a) r

theorem giant_stdAddChar_norm {M : ℕ} [NeZero M] (z : ZMod M) :
    ‖ZMod.stdAddChar z‖ = 1 := by
  rw [ZMod.stdAddChar_apply]
  exact Circle.norm_coe _

theorem giant_stdAddChar_neg {M : ℕ} [NeZero M] (z : ZMod M) :
    ZMod.stdAddChar (-z) = conj (ZMod.stdAddChar z) := by
  rw [ZMod.stdAddChar_apply, ZMod.stdAddChar_apply, AddChar.map_neg_eq_inv,
    Circle.coe_inv_eq_conj]

/-- The actual finite additive Fourier expansion, without a primitive-character hypothesis. -/
theorem giant_character_additive_expansion {M : ℕ} [NeZero M]
    (χ : DirichletCharacter ℂ M) (z : ZMod M) :
    χ z = ∑ r : ZMod M, giantCharacterAdditiveCoefficient χ r * ZMod.stdAddChar (r*z) := by
  have h := congrFun (ZMod.dft.symm_apply_apply (fun a : ZMod M => χ a)) z
  rw [ZMod.invDFT_apply] at h
  simpa only [giantCharacterAdditiveCoefficient, smul_eq_mul, Finset.mul_sum,
    mul_assoc, mul_comm, mul_left_comm] using h.symm

theorem giant_character_additive_coefficient_norm_le {M : ℕ} [NeZero M]
    (χ : DirichletCharacter ℂ M) (r : ZMod M) :
    ‖giantCharacterAdditiveCoefficient χ r‖ ≤ 1 := by
  have hsum : ‖ZMod.dft (fun a : ZMod M => χ a) r‖ ≤ (M : ℝ) := by
    rw [ZMod.dft_apply]
    calc
      _ ≤ ∑ a : ZMod M, ‖ZMod.stdAddChar (-(a*r)) • χ a‖ := norm_sum_le _ _
      _ ≤ ∑ _a : ZMod M, (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro a _
        simpa only [smul_eq_mul, norm_mul, giant_stdAddChar_norm, one_mul] using χ.norm_le_one a
      _ = (M : ℝ) := by simp
  have hM : (M : ℝ) ≠ 0 := by exact_mod_cast (NeZero.ne M)
  rw [giantCharacterAdditiveCoefficient, norm_mul, norm_inv, Complex.norm_natCast]
  exact (mul_le_mul_of_nonneg_left hsum (inv_nonneg.mpr (Nat.cast_nonneg M))).trans_eq
    (inv_mul_cancel₀ hM)

theorem giant_character_additive_l1_le {M : ℕ} [NeZero M]
    (χ : DirichletCharacter ℂ M) :
    (∑ r : ZMod M, ‖giantCharacterAdditiveCoefficient χ r‖) ≤ (M : ℝ) := by
  calc
    _ ≤ ∑ _r : ZMod M, (1 : ℝ) := Finset.sum_le_sum (fun r _ =>
      giant_character_additive_coefficient_norm_le χ r)
    _ = _ := by simp

/-- A multiplier depending on the edge difference is a finite sum of
unit-modulus endpoint multipliers, with conjugation at the source. -/
theorem giant_character_difference_expansion {M : ℕ} [NeZero M]
    (χ : DirichletCharacter ℂ M) (x y : ZMod M) :
    χ (y-x) = ∑ r : ZMod M, giantCharacterAdditiveCoefficient χ r *
      conj (ZMod.stdAddChar (r*x)) * ZMod.stdAddChar (r*y) := by
  rw [giant_character_additive_expansion]
  apply Finset.sum_congr rfl
  intro r _
  rw [mul_sub, sub_eq_add_neg, AddChar.map_add_eq_mul, giant_stdAddChar_neg]
  ring

theorem giant_character_phase_norm {M : ℕ} [NeZero M] (x : ZMod M) (v : ℂ) :
    ‖ZMod.stdAddChar x * v‖ = ‖v‖ := by
  rw [norm_mul, giant_stdAddChar_norm, one_mul]

/-- Literal finite graph pairings commute with the Fourier expansion. -/
theorem giant_character_graph_pairing {M : ℕ} [NeZero M] {α : Type*}
    (χ : DirichletCharacter ℂ M) (S : Finset α) (w : α → ℂ) (x y : α → ZMod M) :
    (∑ a ∈ S, w a * χ (y a-x a)) =
      ∑ r : ZMod M, giantCharacterAdditiveCoefficient χ r *
        ∑ a ∈ S, w a * conj (ZMod.stdAddChar (r*x a)) * ZMod.stdAddChar (r*y a) := by
  simp_rw [giant_character_difference_expansion, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro r _
  apply Finset.sum_congr rfl
  intro a _
  ring

/-- Any uniform bound for the phase-modified original pairings transfers
with a constant depending only on the fixed modulus. -/
theorem giant_character_graph_bound {M : ℕ} [NeZero M] {α : Type*}
    (χ : DirichletCharacter ℂ M) (S : Finset α) (w : α → ℂ) (x y : α → ZMod M)
    {C : ℝ} (hC : 0 ≤ C)
    (hphase : ∀ r : ZMod M,
      ‖∑ a ∈ S, w a * conj (ZMod.stdAddChar (r*x a)) * ZMod.stdAddChar (r*y a)‖ ≤ C) :
    ‖∑ a ∈ S, w a * χ (y a-x a)‖ ≤ (M : ℝ)*C := by
  rw [giant_character_graph_pairing]
  calc
    _ ≤ ∑ r : ZMod M, ‖giantCharacterAdditiveCoefficient χ r *
        ∑ a ∈ S, w a * conj (ZMod.stdAddChar (r*x a)) * ZMod.stdAddChar (r*y a)‖ := norm_sum_le _ _
    _ ≤ ∑ r : ZMod M, ‖giantCharacterAdditiveCoefficient χ r‖ * C := by
      apply Finset.sum_le_sum
      intro r _
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (hphase r) (norm_nonneg _)
    _ = (∑ r : ZMod M, ‖giantCharacterAdditiveCoefficient χ r‖)*C := by rw [Finset.sum_mul]
    _ ≤ (M : ℝ)*C := mul_le_mul_of_nonneg_right (giant_character_additive_l1_le χ) hC

end
end ArtinMatthews
