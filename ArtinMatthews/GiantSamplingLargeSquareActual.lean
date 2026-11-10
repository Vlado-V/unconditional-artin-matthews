module

public import ArtinMatthews.GiantSamplingSquareRows
public import ArtinMatthews.GiantSamplingLargeSquareCount
public import ArtinMatthews.GiantSamplingLargeSquareWeight
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
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
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! The large squarepart error for a literal cofactor box. The divisor
bound is used before summing the product pairs, so the modulus cutoff does
not enter the constant. -/

noncomputable section
namespace ArtinMatthews

open OAI OAI.SevenEighths
open scoped BigOperators

theorem giantCubicSampling_largeSquareRows_le (η : HeckeFamily.Character) {M : ℕ}
    (χ : DirichletCharacter ℂ M) (ν : ℝ) (hν : 0 < ν) :
    ∃ Cν : ℝ, 0 < Cν ∧ ∀ (H : ℕ → ℂ) (Φ : ℝ → ℝ) (ε x T D C : ℝ)
      (R : ℕ) (K : Finset ℕ) (B : ℕ),
      1 ≤ x → 0 < T → 4 ≤ D → 0 ≤ C →
      (∀ k ∈ K, T ≤ (k : ℝ) ∧ (k : ℝ) ≤ 2 * T) →
      (∀ k ∈ K, ‖H k‖ ≤ C) → (∀ t, ‖Φ t‖ ≤ 1) →
      Function.support Φ ⊆ Set.Ioo 1 2 →
      (∑ r ∈ Finset.Icc 1 R, ‖giantCubicSamplingSquareRows η χ H Φ ε x r K B
        ((Finset.Icc 1 B).filter (fun d : ℕ => D < (d : ℝ)))‖) ≤
        Cν * C * x ^ (1 + 2 * ν) / D := by
  obtain ⟨C₀, hC₀, hbound⟩ := giantCubicSampling_supported_sum_moduli_norm_le η χ ν hν
  refine ⟨16 * C₀, by positivity, ?_⟩
  intro H Φ ε x T D C R K B hx hT hD hC hK hH hΦ hs
  let P := (Finset.Icc 1 B).filter (fun d : ℕ => D < (d : ℝ))
  let A := giantSamplingSquarefreeRow K B
  let Q := giantSamplingWindowBelow x ε T
  let f (r d a ℓ : ℕ) := H (d ^ 2 * a) *
    giantCubicSamplingKernel η χ Φ x r (ℓ * (d ^ 2 * a))
  let L := C * C₀ * x ^ (2 * ν)
  have hx₀ : 0 < x := zero_lt_one.trans_le hx
  have hL : 0 ≤ L := mul_nonneg (mul_nonneg hC hC₀.le) (Real.rpow_nonneg hx₀.le _)
  have hrow (r : ℕ) : giantCubicSamplingSquareRows η χ H Φ ε x r K B P =
      ∑ d ∈ P, ∑ a ∈ A d, ∑ ℓ ∈ Q, f r d a ℓ := by
    unfold giantCubicSamplingSquareRows
    apply Finset.sum_congr rfl
    intro d hd
    have hd₀ : 0 < d := (Finset.mem_Icc.mp (Finset.mem_filter.mp hd).1).1
    apply Finset.sum_congr rfl
    intro a ha
    have haK : d ^ 2 * a ∈ K := (Finset.mem_filter.mp ha).2.2
    rw [giantSamplingScaledWindow, Finset.sum_image]
    · change _ = ∑ ℓ ∈ (giantPrimeWindow x ε).filter (fun ℓ : ℕ => (ℓ : ℝ) ≤ 2 * x / T), _
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro ℓ _hℓ
      dsimp only [f]
      rw [show a * (d ^ 2 * ℓ) = ℓ * (d ^ 2 * a) by ac_rfl]
      by_cases hℓ : (ℓ : ℝ) ≤ 2 * x / T
      · simp only [hℓ, ite_true]
      · have hprod : 2 * x < (ℓ : ℝ) * ((d ^ 2 * a : ℕ) : ℝ) :=
          ((div_lt_iff₀ hT).mp (lt_of_not_ge hℓ)).trans_le
            (mul_le_mul_of_nonneg_left (hK _ haK).1 (Nat.cast_nonneg _))
        have hzero : Φ (((ℓ * (d ^ 2 * a) : ℕ) : ℝ) / x) = 0 := by
          by_contra h
          have hup := (div_lt_iff₀ hx₀).mp (hs h).2
          rw [Nat.cast_mul] at hup
          exact (not_lt_of_ge hprod.le) hup
        simp only [Nat.cast_mul, Nat.cast_pow] at hzero
        simp [hℓ, giantCubicSamplingKernel, hzero]
    · intro p _hp q _hq heq
      exact Nat.eq_of_mul_eq_mul_left (pow_pos hd₀ _) heq
  have hcardP : (∑ d ∈ P, ((A d).card : ℝ)) ≤ 8 * T / D :=
    giantSampling_largeSquareRow_card_sum_le K B hT.le hD (fun k hk => (hK k hk).2)
  have hcardQ : (Q.card : ℝ) ≤ 2 * x / T := giantSamplingWindowBelow_card_le hx₀.le hT
  calc
    _ ≤ ∑ r ∈ Finset.Icc 1 R, ∑ d ∈ P, ∑ a ∈ A d, ∑ ℓ ∈ Q, ‖f r d a ℓ‖ := by
      apply Finset.sum_le_sum
      intro r _hr
      rw [hrow]
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro d _hd
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro a _ha
      exact norm_sum_le _ _
    _ = ∑ d ∈ P, ∑ a ∈ A d, ∑ ℓ ∈ Q, ∑ r ∈ Finset.Icc 1 R, ‖f r d a ℓ‖ := by
      rw [Finset.sum_comm (s := Finset.Icc 1 R) (t := P)]
      apply Finset.sum_congr rfl
      intro d _hd
      rw [Finset.sum_comm (s := Finset.Icc 1 R) (t := A d)]
      apply Finset.sum_congr rfl
      intro a _ha
      rw [Finset.sum_comm (s := Finset.Icc 1 R) (t := Q)]
    _ ≤ ∑ d ∈ P, ∑ _a ∈ A d, ∑ _ℓ ∈ Q, L := by
      apply Finset.sum_le_sum
      intro d _hd
      apply Finset.sum_le_sum
      intro a ha
      have hk : d ^ 2 * a ∈ K := (Finset.mem_filter.mp ha).2.2
      exact Finset.sum_le_sum fun ℓ _ => hbound Φ x R (ℓ * (d ^ 2 * a))
        (H (d ^ 2 * a)) C hx hC (hH _ hk) hΦ hs
    _ = (∑ d ∈ P, ((A d).card : ℝ)) * (Q.card : ℝ) * L := by
      simp only [Finset.sum_const, nsmul_eq_mul, Finset.sum_mul, mul_assoc]
    _ ≤ (8 * T / D) * (2 * x / T) * L :=
      mul_le_mul_of_nonneg_right (mul_le_mul hcardP hcardQ (Nat.cast_nonneg _)
        (by positivity)) hL
    _ = _ := by
      rw [Real.rpow_add hx₀, Real.rpow_one]
      dsimp only [L]
      field_simp [hT.ne']
      ring

end ArtinMatthews
