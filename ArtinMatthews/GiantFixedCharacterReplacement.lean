module

public import ArtinMatthews.MarkedMajorArcLongCoefficient
public import ArtinMatthews.HeckeDirichletProduct
public import ArtinMatthews.MarkedTypeIICoefficients
public import Mathlib.NumberTheory.DirichletCharacter.Bounds


set_option backward.privateInPublic true
@[expose] public section

/-! The actual fixed-character replacement coefficient of paper (3.3).
Its complete long-character test follows from the proved centered prime-minus-
rough estimate at the product modulus, including nonunits and conjugation. -/
namespace ArtinMatthews
noncomputable section
open Filter
open scoped BigOperators Topology ComplexConjugate

def giantFixedCharacterReplacementCoefficient {M : ℕ} (χ : DirichletCharacter ℂ M)
    (W modulation : ℝ) (n : ℕ) : ℂ :=
  χ n * markedMajorCenteredCoefficient W modulation n

/-- Multiplication by the fixed character does not enlarge support or size. -/
theorem giantFixedCharacterReplacementCoefficient_norm_le {M : ℕ}
    (χ : DirichletCharacter ℂ M) (W modulation : ℝ) (n : ℕ) :
    ‖giantFixedCharacterReplacementCoefficient χ W modulation n‖ ≤
      ‖markedMajorCenteredCoefficient W modulation n‖ := by
  rw [giantFixedCharacterReplacementCoefficient, norm_mul]
  exact mul_le_of_le_one_left (norm_nonneg _) (χ.norm_le_one _)

theorem giantFixedCharacterReplacementCoefficient_ne_zero {M : ℕ}
    (χ : DirichletCharacter ℂ M) (W modulation : ℝ) (n : ℕ)
    (hn : giantFixedCharacterReplacementCoefficient χ W modulation n ≠ 0) :
    markedMajorCenteredCoefficient W modulation n ≠ 0 :=
  (mul_ne_zero_iff.mp hn).2

/-- Exact product-character testing at every integer, with characters extended
by zero on nonunits. The interval contains only positive integers. -/
theorem giantFixedCharacterReplacement_test {M q : ℕ}
    (χ : DirichletCharacter ℂ M) (ϑ : DirichletCharacter ℂ q)
    (W modulation t H u v : ℝ) :
    (H : ℂ)⁻¹ * markedTwistedSum (Finset.Ioc ⌊u⌋₊ ⌊v⌋₊)
        (giantFixedCharacterReplacementCoefficient χ W modulation) ϑ t =
      markedMajorCenteredSum (heckeDirichletProduct χ ϑ) W modulation t H u v := by
  unfold markedTwistedSum markedMajorCenteredSum
  congr 1
  apply Finset.sum_congr rfl
  intro n hn
  have hn0 : 0 < n := (Nat.zero_le _).trans_lt (Finset.mem_Ioc.mp hn).1
  rw [heckeDirichletProduct_natCast, markedLogTwist_eq_cpow hn0]
  unfold giantFixedCharacterReplacementCoefficient
  rw [mul_comm Complex.I (t : ℂ)]
  ring

/-- A fixed modulus costs exactly one extra logarithmic exponent eventually. -/
theorem giantFixedCharacter_product_modulus (M : ℕ) (a : ℝ) :
    ∀ᶠ L : ℝ in atTop, ∀ q : ℕ, (q : ℝ) ≤ L^a → (M*q : ℕ) ≤ L^(a+1) := by
  filter_upwards [eventually_ge_atTop (M : ℝ), eventually_gt_atTop (0 : ℝ)] with L hM hL
  intro q hq
  have hprod : (M : ℝ)*(q : ℝ) ≤ L*L^a :=
    mul_le_mul hM hq (Nat.cast_nonneg _) hL.le
  simpa only [Nat.cast_mul, Real.rpow_add hL, Real.rpow_one, mul_comm] using hprod

/-- Full long-frequency criterion for the literal replacement coefficient.
The prime-minus-rough cancellation is a proved input, not an assumption. -/
theorem giant_fixed_character_replacement_all_log {M : ℕ} [NeZero M]
    (χ : DirichletCharacter ℂ M) (a η τ C b K P : ℝ)
    (ha : 0 ≤ a) (hη : 0 < η) (hτ : 0 < τ) (hC : 0 ≤ C) (hP : 0 ≤ P) :
    ∀ᶠ L : ℝ in atTop,
      ∀ (q : ℕ) [NeZero q] (ϑ : DirichletCharacter ℂ q) (modulation t H u v : ℝ),
        (q : ℝ) ≤ L^a → |modulation| ≤ L^C → |t| ≤ K*Real.exp L*L^b →
        Real.exp (τ*L) ≤ H → H ≤ u → u ≤ v → v ≤ 2*H → v ≤ Real.exp (η*L) →
        ‖markedTwistedSum (Finset.Ioc ⌊u⌋₊ ⌊v⌋₊)
          (giantFixedCharacterReplacementCoefficient χ (Real.exp (L^(6/25 : ℝ))) modulation)
          ϑ t‖ / H ≤ L^(-P) := by
  filter_upwards [marked_major_long_coefficient (a+1) η τ C b K P
      (by linarith) hη hτ hC hP,
    giantFixedCharacter_product_modulus M a] with L hlong hmod
  intro q _ ϑ modulation t H u v hq hm ht hH hHu huv hvH hvhi
  have htest := hlong (M*q) (heckeDirichletProduct χ ϑ) modulation t H u v
    (hmod q hq) hm ht hH hHu huv hvH hvhi
  rw [← giantFixedCharacterReplacement_test] at htest
  have hH0 : 0 < H := (Real.exp_pos _).trans_le hH
  have hnorm : ‖(H : ℂ)⁻¹ * markedTwistedSum (Finset.Ioc ⌊u⌋₊ ⌊v⌋₊)
      (giantFixedCharacterReplacementCoefficient χ (Real.exp (L^(6/25 : ℝ))) modulation) ϑ t‖ =
      ‖markedTwistedSum (Finset.Ioc ⌊u⌋₊ ⌊v⌋₊)
        (giantFixedCharacterReplacementCoefficient χ (Real.exp (L^(6/25 : ℝ))) modulation) ϑ t‖ / H := by
    rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hH0]
    ring
  rwa [hnorm] at htest

/-- The same criterion for the conjugated actual replacement coefficient. -/
theorem giant_fixed_character_replacement_conjugate_all_log {M : ℕ} [NeZero M]
    (χ : DirichletCharacter ℂ M) (a η τ C b K P : ℝ)
    (ha : 0 ≤ a) (hη : 0 < η) (hτ : 0 < τ) (hC : 0 ≤ C) (hP : 0 ≤ P) :
    ∀ᶠ L : ℝ in atTop,
      ∀ (q : ℕ) [NeZero q] (ϑ : DirichletCharacter ℂ q) (modulation t H u v : ℝ),
        (q : ℝ) ≤ L^a → |modulation| ≤ L^C → |t| ≤ K*Real.exp L*L^b →
        Real.exp (τ*L) ≤ H → H ≤ u → u ≤ v → v ≤ 2*H → v ≤ Real.exp (η*L) →
        ‖markedTwistedSum (Finset.Ioc ⌊u⌋₊ ⌊v⌋₊)
          (fun n => conj (giantFixedCharacterReplacementCoefficient χ
            (Real.exp (L^(6/25 : ℝ))) modulation n)) ϑ t‖ / H ≤ L^(-P) := by
  filter_upwards [giant_fixed_character_replacement_all_log χ a η τ C b K P ha hη hτ hC hP]
    with L hlong
  intro q _ ϑ modulation t H u v hq hm ht hH hHu huv hvH hvhi
  have htest := hlong q (star ϑ) modulation (-t) H u v hq hm
    (by simpa only [abs_neg] using ht) hH hHu huv hvH hvhi
  have heq := markedTwistedSum_norm_conjugate (Finset.Ioc ⌊u⌋₊ ⌊v⌋₊)
    (giantFixedCharacterReplacementCoefficient χ (Real.exp (L^(6/25 : ℝ))) modulation)
    (star ϑ) t
  simp only [star_star] at heq
  rw [heq]
  exact htest

end
end ArtinMatthews
