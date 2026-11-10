module

public import ArtinMatthews.SpectralBareModulusSeries
public import ArtinMatthews.SpectralCuspEisensteinWidthFormula
public import ArtinMatthews.SpectralABLSameCuspAtkinLehner
public import ArtinMatthews.SpectralCuspEisensteinInfinity
public import ArtinMatthews.SpectralInfinityKloostermanWeil
public import ArtinMatthews.SpectralMixedSameCuspKloosterman
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
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
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! The actual identity cusp and the actual 1/N cusp give the same
diagonal bare geometric fibre at each positive raw modulus. -/

noncomputable section
open Set
open scoped MatrixGroups

namespace ArtinMatthews

private theorem infinity_diagonalKloosterman_eq_oneOver (N c : ℕ) [NeZero N] [NeZero c]
    (n : ℤ) : gamma0TrueWidthKloostermanSum N 1 1 c n n =
      gamma0TrueWidthKloostermanSum N (gamma0CuspOneOver N) (gamma0CuspOneOver N) c n n := by
  by_cases hc : N ∣ c
  · obtain ⟨d, rfl⟩ := hc
    have hd : d ≠ 0 := fun h => NeZero.ne (N*d) (by rw [h, Nat.mul_zero])
    let _ : NeZero d := ⟨hd⟩
    rw [gamma0TrueWidthKloostermanSum_identity_eq_standard, ite_eq_left (dvd_mul_right N d)]
    simpa only [one_mul] using
      (gamma0MixedSameCuspKloosterman_diag_eq_standard 1 N d (Nat.coprime_one_left N) n).symm
  · rw [gamma0TrueWidthKloostermanSum_identity_eq_standard, ite_eq_right hc]
    simpa only [one_mul] using
      (gamma0MixedSameCuspKloosterman_zero_of_not_dvd 1 N c hc n n).symm

theorem gamma0Infinity_bareFibre_eq_oneOver (N : ℕ) [NeZero N]
    (c : Ioi (0 : ℕ)) (n : ℤ) (H : ℂ → ℂ) :
    gamma0TrueWidthBareFibre N 1 1 c n n H =
      gamma0TrueWidthBareFibre N (gamma0CuspOneOver N) (gamma0CuspOneOver N) c n n H := by
  let _ : NeZero c.val := ⟨c.property.ne'⟩
  have hinfty : gamma0TrueWidthModulus N 1 1 (c.val : ℝ) = (c.val : ℝ) := by
    simp [gamma0TrueWidthModulus, gamma0CuspTrueWidth_identity]
  have honeOver : gamma0TrueWidthModulus N (gamma0CuspOneOver N) (gamma0CuspOneOver N)
      (c.val : ℝ) = (c.val : ℝ) := by
    simpa only [one_mul] using gamma0AtkinSameCusp_modulus 1 N c.val (Nat.coprime_one_left N)
  unfold gamma0TrueWidthBareFibre
  dsimp only
  rw [hinfty, honeOver, infinity_diagonalKloosterman_eq_oneOver N c.val n]

theorem gamma0Infinity_bareFibre_zero (N : ℕ) [NeZero N] (c : Ioi (0 : ℕ))
    (hc : ¬ N ∣ c.val) (n : ℤ) (H : ℂ → ℂ) :
    gamma0TrueWidthBareFibre N 1 1 c n n H = 0 := by
  let _ : NeZero c.val := ⟨c.property.ne'⟩
  simp only [gamma0TrueWidthBareFibre, gamma0TrueWidthKloostermanSum_identity_eq_standard,
    ite_eq_right hc, zero_mul]

end ArtinMatthews
