module

public import Mathlib.Analysis.Fourier.FiniteAbelian.PontryaginDuality
public import Mathlib.NumberTheory.DirichletCharacter.Basic
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.Measurability.Init
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar


set_option backward.privateInPublic true
@[expose] public section

/-!
# Exact character separation in the marked determinant major term

The major-arc argument in PD Section 5 first expands the phase on the six
unit variables modulo a logarithmic modulus. This module proves that exact
finite Fourier step and its coefficient cost. It does not assert the later
Mellin, sparse-frequency, or minor-arc estimates.
-/

noncomputable section
open scoped BigOperators ComplexConjugate

namespace ArtinMatthews

section FiniteFourier

variable {G : Type*} [AddCommGroup G] [Fintype G]

/-- Normalized Fourier coefficient, with the negative sign in the character. -/
def markedFourierCoeff (f : G → ℂ) (χ : AddChar G ℂ) : ℂ :=
  (∑ g : G, f g * χ (-g)) / Fintype.card G

/-- Fourier inversion for an arbitrary function, including the determinant phase. -/
theorem marked_fourier_inversion (f : G → ℂ) (x : G) :
    f x = ∑ χ : AddChar G ℂ, markedFourierCoeff f χ * χ x := by
  classical
  have hcard : (Fintype.card G : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  symm
  calc
    _ = (∑ χ : AddChar G ℂ, ∑ g : G, f g * χ (x - g)) / Fintype.card G := by
      simp only [markedFourierCoeff, div_mul_eq_mul_div, Finset.sum_mul,
        ← Finset.sum_div]
      congr 1
      apply Finset.sum_congr rfl
      intro χ _
      apply Finset.sum_congr rfl
      intro g _
      rw [sub_eq_add_neg, AddChar.map_add_eq_mul]
      ring
    _ = (∑ g : G, f g * ∑ χ : AddChar G ℂ, χ (x - g)) / Fintype.card G := by
      rw [Finset.sum_comm]
      simp_rw [Finset.mul_sum]
    _ = (∑ g : G, f g * if x = g then (Fintype.card G : ℂ) else 0) /
        Fintype.card G := by simp_rw [AddChar.sum_apply_eq_ite, sub_eq_zero]
    _ = f x := by simp [hcard]

/-- A bounded phase has bounded normalized Fourier coefficients. -/
theorem markedFourierCoeff_norm_le (f : G → ℂ) {C : ℝ}
    (hf : ∀ g, ‖f g‖ ≤ C) (χ : AddChar G ℂ) :
    ‖markedFourierCoeff f χ‖ ≤ C := by
  have hcard : (0 : ℝ) < Fintype.card G := Nat.cast_pos.mpr Fintype.card_pos
  rw [markedFourierCoeff, norm_div, Complex.norm_natCast]
  apply (div_le_iff₀ hcard).mpr
  calc
    ‖∑ g : G, f g * χ (-g)‖ ≤ ∑ g : G, ‖f g * χ (-g)‖ := norm_sum_le _ _
    _ ≤ ∑ _g : G, C := by
      apply Finset.sum_le_sum
      intro g _
      simpa only [norm_mul, AddChar.norm_apply, mul_one] using hf g
    _ = C * Fintype.card G := by simp [mul_comm]

/-- The total absolute Fourier coefficient mass costs at most the group size. -/
theorem markedFourierCoeff_total_norm_le (f : G → ℂ) {C : ℝ}
    (hf : ∀ g, ‖f g‖ ≤ C) :
    (∑ χ : AddChar G ℂ, ‖markedFourierCoeff f χ‖) ≤ Fintype.card G * C := by
  calc
    _ ≤ ∑ _χ : AddChar G ℂ, C :=
      Finset.sum_le_sum (fun χ _ => markedFourierCoeff_norm_le f hf χ)
    _ = Fintype.card G * C := by simp

end FiniteFourier

section CoordinateCharacters

variable {ι A : Type*} [Fintype ι] [DecidableEq ι] [AddCommGroup A]

/-- Restrict a character of a tuple to one coordinate subgroup. -/
def markedCoordinateChar (χ : AddChar (ι → A) ℂ) (i : ι) : AddChar A ℂ where
  toFun a := χ (Pi.single i a)
  map_zero_eq_one' := by simp
  map_add_eq_mul' a b := by
    rw [Pi.single_add, AddChar.map_add_eq_mul]

omit [Fintype ι] in
/-- The finite-sum form of the character homomorphism identity. -/
theorem marked_character_map_sum {B : Type*} [AddCommGroup B]
    (χ : AddChar B ℂ) (S : Finset ι) (v : ι → B) :
    χ (∑ i ∈ S, v i) = ∏ i ∈ S, χ (v i) := by
  induction S using Finset.induction_on with
  | empty => simp
  | @insert i S hi ih => simp [hi, AddChar.map_add_eq_mul, ih]

/-- A character of the six-variable group is the product of six individual
characters. The statement also applies to any finite number of coordinates. -/
theorem marked_character_coordinate_product (χ : AddChar (ι → A) ℂ) (x : ι → A) :
    χ x = ∏ i, markedCoordinateChar χ i (x i) := by
  have hx : (∑ i, Pi.single i (x i)) = x := by
    ext j
    simp
  conv_lhs => rw [← hx]
  rw [marked_character_map_sum]
  rfl

/-- The exact scalar separation of a finite phase sum. After inserting the
six-variable phase, each term is a product of six one-variable character sums. -/
theorem marked_fourier_product_separation [Fintype A]
    (S : ι → Finset A) (c : ι → A → ℂ) (f : (ι → A) → ℂ) :
    (∑ x ∈ Fintype.piFinset S, (∏ i, c i (x i)) * f x) =
      ∑ χ : AddChar (ι → A) ℂ, markedFourierCoeff f χ *
        ∏ i, ∑ a ∈ S i, c i a * markedCoordinateChar χ i a := by
  classical
  simp_rw [marked_fourier_inversion f, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro χ _
  calc
    (∑ x ∈ Fintype.piFinset S,
        (∏ i, c i (x i)) * (markedFourierCoeff f χ * χ x)) =
        markedFourierCoeff f χ * ∑ x ∈ Fintype.piFinset S,
          ∏ i, c i (x i) * markedCoordinateChar χ i (x i) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x _
      rw [marked_character_coordinate_product, Finset.prod_mul_distrib]
      ring
    _ = _ := by rw [Finset.prod_univ_sum]

/-- The same separation on arbitrary finite coefficient supports pulled back
to residue classes. In particular, the supports may be long integer intervals;
their size does not appear in the finite Fourier coefficient cost. -/
theorem marked_fourier_product_pullback [Fintype A] {D : ι → Type*}
    (S : ∀ i, Finset (D i)) (c : ∀ i, D i → ℂ) (r : ∀ i, D i → A)
    (f : (ι → A) → ℂ) :
    (∑ x ∈ Fintype.piFinset S, (∏ i, c i (x i)) * f (fun i => r i (x i))) =
      ∑ χ : AddChar (ι → A) ℂ, markedFourierCoeff f χ *
        ∏ i, ∑ a ∈ S i, c i a * markedCoordinateChar χ i (r i a) := by
  classical
  simp_rw [marked_fourier_inversion f, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro χ _
  calc
    (∑ x ∈ Fintype.piFinset S, (∏ i, c i (x i)) *
        (markedFourierCoeff f χ * χ (fun i => r i (x i)))) =
        markedFourierCoeff f χ * ∑ x ∈ Fintype.piFinset S,
          ∏ i, c i (x i) * markedCoordinateChar χ i (r i (x i)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x _
      rw [marked_character_coordinate_product, Finset.prod_mul_distrib]
      ring
    _ = _ := by rw [Finset.prod_univ_sum]

end CoordinateCharacters

/-- Six unit variables in additive notation. -/
abbrev MarkedUnitTuple (k : ℕ) := Fin 6 → Additive ((ZMod k)ˣ)

/-- One coordinate character, viewed as a homomorphism into the complex units. -/
def markedCoordinateUnitHom (k : ℕ) [NeZero k]
    (χ : AddChar (MarkedUnitTuple k) ℂ) (i : Fin 6) : (ZMod k)ˣ →* ℂˣ where
  toFun u := Units.mk0 (markedCoordinateChar χ i (Additive.ofMul u)) (by
    intro hzero
    have hnorm := (markedCoordinateChar χ i).norm_apply (Additive.ofMul u)
    simp [hzero] at hnorm)
  map_one' := by
    apply Units.ext
    simp [markedCoordinateChar]
  map_mul' u v := by
    apply Units.ext
    exact (markedCoordinateChar χ i).map_add_eq_mul
      (Additive.ofMul u) (Additive.ofMul v)

/-- The multiplicative character used in the six-variable major-arc expansion,
extended by zero on nonunits as in the source. -/
def markedCoordinateDirichlet (k : ℕ) [NeZero k]
    (χ : AddChar (MarkedUnitTuple k) ℂ) (i : Fin 6) : DirichletCharacter ℂ k :=
  MulChar.ofUnitHom (markedCoordinateUnitHom k χ i)

@[simp] theorem markedCoordinateDirichlet_unit (k : ℕ) [NeZero k]
    (χ : AddChar (MarkedUnitTuple k) ℂ) (i : Fin 6) (u : (ZMod k)ˣ) :
    markedCoordinateDirichlet k χ i (u : ZMod k) =
      markedCoordinateChar χ i (Additive.ofMul u) := by
  simp [markedCoordinateDirichlet, markedCoordinateUnitHom]

/-- A tuple character is exactly a product of six zero-extended Dirichlet characters
when evaluated on the six unit coordinates. -/
theorem marked_tuple_character_eq_dirichlet_product (k : ℕ) [NeZero k]
    (χ : AddChar (MarkedUnitTuple k) ℂ) (x : MarkedUnitTuple k) :
    χ x = ∏ i : Fin 6,
      markedCoordinateDirichlet k χ i ((Additive.toMul (x i) : (ZMod k)ˣ) : ZMod k) := by
  simpa only [markedCoordinateDirichlet_unit, ofMul_toMul] using
    marked_character_coordinate_product χ x

/-- The natural representative of a coordinate of the six-unit tuple. -/
def markedUnitRepresentative {k : ℕ} (x : MarkedUnitTuple k) (i : Fin 6) : ℕ :=
  (↑(Additive.toMul (x i)) : ZMod k).val

/-- The integer phase `bmn - ars - b + a`, in the paper's variable order
`(a,b,m,n,r,s)`. -/
def markedResidueDeterminant {k : ℕ} (x : MarkedUnitTuple k) : ℤ :=
  (markedUnitRepresentative x 1 : ℤ) * markedUnitRepresentative x 2 *
      markedUnitRepresentative x 3 -
    (markedUnitRepresentative x 0 : ℤ) * markedUnitRepresentative x 4 *
      markedUnitRepresentative x 5 -
    markedUnitRepresentative x 1 + markedUnitRepresentative x 0

/-- The residue phase on one rational major arc. -/
def markedResiduePhase (k : ℕ) (h : ℤ) (x : MarkedUnitTuple k) : ℂ :=
  Complex.exp (Complex.I * (2 * Real.pi * h * markedResidueDeterminant x / k : ℝ))

/-- The same phase as the canonical additive character modulo `k`. -/
theorem markedResiduePhase_eq_zmod (k : ℕ) [NeZero k] (h : ℤ)
    (x : MarkedUnitTuple k) :
    markedResiduePhase k h x =
      ((AddChar.zmod k (h : ZMod k) (markedResidueDeterminant x : ZMod k) : Circle) : ℂ) := by
  rw [AddChar.zmod_intCast, Circle.coe_exp]
  unfold markedResiduePhase
  congr 1
  push_cast
  ring

/-- The determinant polynomial in the residue ring, with the six unit inputs. -/
def markedResidueDeterminantZMod {k : ℕ} (x : MarkedUnitTuple k) : ZMod k :=
  (Additive.toMul (x 1) : (ZMod k)ˣ).val * (Additive.toMul (x 2) : (ZMod k)ˣ).val *
      (Additive.toMul (x 3) : (ZMod k)ˣ).val -
    (Additive.toMul (x 0) : (ZMod k)ˣ).val * (Additive.toMul (x 4) : (ZMod k)ˣ).val *
      (Additive.toMul (x 5) : (ZMod k)ˣ).val -
    (Additive.toMul (x 1) : (ZMod k)ˣ).val + (Additive.toMul (x 0) : (ZMod k)ˣ).val

theorem markedResidueDeterminant_cast (k : ℕ) [NeZero k] (x : MarkedUnitTuple k) :
    (markedResidueDeterminant x : ZMod k) = markedResidueDeterminantZMod x := by
  simp [markedResidueDeterminant, markedUnitRepresentative, markedResidueDeterminantZMod]

/-- The six-integer determinant phase agrees with the unit-tuple phase whenever
the coordinates represent the same residue classes. This justifies applying the
finite character expansion to the original integer endpoint variables. -/
theorem marked_integer_phase_eq (k : ℕ) [NeZero k] (h : ℤ)
    (z : Fin 6 → ℤ) (x : MarkedUnitTuple k)
    (hx : ∀ i, (z i : ZMod k) = (Additive.toMul (x i) : (ZMod k)ˣ).val) :
    Complex.exp (Complex.I * (2 * Real.pi * h *
      (z 1 * z 2 * z 3 - z 0 * z 4 * z 5 - z 1 + z 0) / k : ℝ)) =
      markedResiduePhase k h x := by
  rw [markedResiduePhase_eq_zmod]
  have hz : ((z 1 * z 2 * z 3 - z 0 * z 4 * z 5 - z 1 + z 0 : ℤ) : ZMod k) =
      (markedResidueDeterminant x : ZMod k) := by
    rw [markedResidueDeterminant_cast]
    simp only [Int.cast_add, Int.cast_sub, Int.cast_mul, hx, markedResidueDeterminantZMod]
  rw [← hz, AddChar.zmod_intCast, Circle.coe_exp]
  congr 1
  push_cast
  ring

theorem markedResiduePhase_norm (k : ℕ) (h : ℤ) (x : MarkedUnitTuple k) :
    ‖markedResiduePhase k h x‖ = 1 := by
  simp [markedResiduePhase, Complex.norm_exp]

/-- Exact separation of the rational determinant phase, with coefficient norm
at most one and total norm at most `φ(k)^6`. No factor involves the number of
marking bands or their exponents. -/
theorem markedResiduePhase_fourier (k : ℕ) [NeZero k] (h : ℤ) :
    (∀ x : MarkedUnitTuple k,
      markedResiduePhase k h x =
        ∑ χ : AddChar (MarkedUnitTuple k) ℂ,
          markedFourierCoeff (markedResiduePhase k h) χ * χ x) ∧
    (∀ χ : AddChar (MarkedUnitTuple k) ℂ,
      ‖markedFourierCoeff (markedResiduePhase k h) χ‖ ≤ 1) ∧
    (∑ χ : AddChar (MarkedUnitTuple k) ℂ,
      ‖markedFourierCoeff (markedResiduePhase k h) χ‖) ≤
        (Nat.totient k : ℝ) ^ 6 := by
  have hf : ∀ x : MarkedUnitTuple k, ‖markedResiduePhase k h x‖ ≤ 1 :=
    fun x => (markedResiduePhase_norm k h x).le
  refine ⟨marked_fourier_inversion _, fun χ => markedFourierCoeff_norm_le _ hf χ, ?_⟩
  convert markedFourierCoeff_total_norm_le (markedResiduePhase k h) hf using 1
  simp [MarkedUnitTuple, ZMod.card_units_eq_totient]

/-- The elementary `k^6` character cost used after summing over logarithmic moduli. -/
theorem markedResiduePhase_total_norm_le (k : ℕ) [NeZero k] (h : ℤ) :
    (∑ χ : AddChar (MarkedUnitTuple k) ℂ,
      ‖markedFourierCoeff (markedResiduePhase k h) χ‖) ≤ (k : ℝ) ^ 6 := by
  apply (markedResiduePhase_fourier k h).2.2.trans
  exact_mod_cast Nat.pow_le_pow_left (Nat.totient_le k) 6

end ArtinMatthews
