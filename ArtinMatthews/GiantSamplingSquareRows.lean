module

public import ArtinMatthews.GiantSamplingSquarepart
public import ArtinMatthews.GiantSamplingCofactors
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
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! The cofactor rows in the large-prime term split into the actual
square-part ranges. The small-part row has the scaled second variable. -/

noncomputable section
namespace ArtinMatthews

open OAI OAI.SevenEighths
open scoped BigOperators

def giantSamplingSquarefreeRow (K : Finset ℕ) (B d : ℕ) : Finset ℕ := by
  classical
  exact (Finset.Icc 1 B).filter fun a => Squarefree a ∧ d ^ 2 * a ∈ K

theorem giantSquarepartCarrier_sum_rows {A : Type*} [AddCommMonoid A]
    (K : Finset ℕ) (B : ℕ) (F : ℕ → ℕ → A) :
    (∑ t ∈ giantSquarepartCarrier K B, F t.1 t.2) =
      ∑ d ∈ Finset.Icc 1 B, ∑ a ∈ giantSamplingSquarefreeRow K B d, F d a := by
  classical
  rw [giantSquarepartCarrier, Finset.sum_filter, Finset.sum_product]
  apply Finset.sum_congr rfl
  intro d _hd
  rw [giantSamplingSquarefreeRow, Finset.sum_filter]

def giantSamplingScaledWindow (x ε : ℝ) (d : ℕ) : Finset ℕ :=
  (giantPrimeWindow x ε).image (fun ℓ => d ^ 2 * ℓ)

theorem mem_giantSamplingScaledWindow {x ε : ℝ} {d n : ℕ} (hd : 0 < d) :
    n ∈ giantSamplingScaledWindow x ε d ↔ d ^ 2 ∣ n ∧ n / d ^ 2 ∈ giantPrimeWindow x ε := by
  rw [giantSamplingScaledWindow, Finset.mem_image]
  constructor
  · rintro ⟨ℓ, hℓ, rfl⟩
    exact ⟨dvd_mul_right _ _, by simpa only [Nat.mul_div_cancel_left ℓ (pow_pos hd 2)] using hℓ⟩
  · rintro ⟨hn, hq⟩
    exact ⟨n / d ^ 2, hq, Nat.mul_div_cancel' hn⟩

def giantCubicSamplingSquareRows (η : HeckeFamily.Character) {M : ℕ}
    (χ : DirichletCharacter ℂ M) (H : ℕ → ℂ) (Φ : ℝ → ℝ) (ε x : ℝ)
    (r : ℕ) (K : Finset ℕ) (B : ℕ) (D : Finset ℕ) : ℂ :=
  ∑ d ∈ D, ∑ a ∈ giantSamplingSquarefreeRow K B d,
    ∑ n ∈ giantSamplingScaledWindow x ε d,
      H (d ^ 2 * a) * giantCubicSamplingKernel η χ Φ x r (a * n)

theorem giantCubicSamplingCofactorSum_eq_squareRows (η : HeckeFamily.Character) {M : ℕ}
    (χ : DirichletCharacter ℂ M) (H : ℕ → ℂ) (Φ : ℝ → ℝ) (ε x : ℝ)
    (r : ℕ) (K : Finset ℕ) (B : ℕ) (hK : ∀ k ∈ K, 0 < k ∧ k ≤ B) :
    giantCubicSamplingCofactorSum η χ H Φ ε x r K =
      giantCubicSamplingSquareRows η χ H Φ ε x r K B (Finset.Icc 1 B) := by
  classical
  unfold giantCubicSamplingCofactorSum giantCubicSamplingSquareRows
  have hrow (ℓ : ℕ) :
      (∑ k ∈ K, H k * giantCubicSamplingKernel η χ Φ x r (ℓ * k)) =
        ∑ d ∈ Finset.Icc 1 B, ∑ a ∈ giantSamplingSquarefreeRow K B d,
          H (d ^ 2 * a) * giantCubicSamplingKernel η χ Φ x r (ℓ * (d ^ 2 * a)) :=
    (giantSquarepartCarrier_sum K B hK
      (fun k => H k * giantCubicSamplingKernel η χ Φ x r (ℓ * k))).trans
      (giantSquarepartCarrier_sum_rows K B (fun d a =>
        H (d ^ 2 * a) * giantCubicSamplingKernel η χ Φ x r (ℓ * (d ^ 2 * a))))
  simp_rw [hrow]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro d hd
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _ha
  rw [giantSamplingScaledWindow, Finset.sum_image]
  · apply Finset.sum_congr rfl
    intro ℓ _hℓ
    rw [show ℓ * (d ^ 2 * a) = a * (d ^ 2 * ℓ) by ac_rfl]
  · intro p _hp q _hq heq
    exact Nat.eq_of_mul_eq_mul_left (pow_pos (Finset.mem_Icc.mp hd).1 _) heq

theorem giantCubicSamplingCofactorSum_split_squareRows (η : HeckeFamily.Character) {M : ℕ}
    (χ : DirichletCharacter ℂ M) (H : ℕ → ℂ) (Φ : ℝ → ℝ) (ε x : ℝ)
    (r : ℕ) (K : Finset ℕ) (B : ℕ) (hK : ∀ k ∈ K, 0 < k ∧ k ≤ B) (D : ℝ) :
    giantCubicSamplingCofactorSum η χ H Φ ε x r K =
      giantCubicSamplingSquareRows η χ H Φ ε x r K B
          ((Finset.Icc 1 B).filter (fun d => (d : ℝ) ≤ D)) +
        giantCubicSamplingSquareRows η χ H Φ ε x r K B
          ((Finset.Icc 1 B).filter (fun d => D < (d : ℝ))) := by
  rw [giantCubicSamplingCofactorSum_eq_squareRows η χ H Φ ε x r K B hK]
  unfold giantCubicSamplingSquareRows
  simpa only [not_le] using (Finset.sum_filter_add_sum_filter_not
    (s := Finset.Icc 1 B) (p := fun d : ℕ => (d : ℝ) ≤ D)
    (f := fun d => ∑ a ∈ giantSamplingSquarefreeRow K B d,
      ∑ n ∈ giantSamplingScaledWindow x ε d,
        H (d ^ 2 * a) * giantCubicSamplingKernel η χ Φ x r (a * n))).symm

end ArtinMatthews
