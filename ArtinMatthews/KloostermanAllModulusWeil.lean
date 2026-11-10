module

public import ArtinMatthews.KloostermanFourthMoment
public import OAI.NumberTheory.Jacobsthal.Estimates.PairCollisionCount
public import ArtinMatthews.KloostermanCompositeWeil
public import ArtinMatthews.KloostermanWeakBound
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
public import OAI.NumberTheory.Jacobsthal.Sieve.DivisorLogGrowth


set_option backward.privateInPublic true
@[expose] public section

/-! The actual uniform all-modulus Weil input, with the full frequency gcd factor. -/
noncomputable section
open OAI.Erdos970.ErdosKloosterman
namespace ArtinMatthews

theorem standardKloosterman_weil_bound {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ) [NeZero N] (h k : ℤ),
      ‖standardSum N h k‖ ≤ C*(N:ℝ)^((1/2:ℝ)+ε)*
        ((Nat.gcd N (Int.gcd h k):ℕ):ℝ)^(1/2:ℝ) := by
  obtain ⟨C,hC,hdiv⟩ := OAI.Erdos970.ErdosDivisorBounds.divisor_power_subpower 3 hε
  refine ⟨C,hC,?_⟩
  intro N _inst h k
  have hN : 0 < (N:ℝ) := by exact_mod_cast NeZero.pos N
  have hd := hdiv N NeZero.one_le
  calc
    _ ≤ (N.divisors.card:ℝ)^3*Real.sqrt N*Real.sqrt ((Nat.gcd N (Int.gcd h k):ℕ):ℝ) :=
      PrimePowerWeil.standardSum_weil_divisor_bound N h k
    _ ≤ (C*(N:ℝ)^ε)*Real.sqrt N*Real.sqrt ((Nat.gcd N (Int.gcd h k):ℕ):ℝ) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hd (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _)
    _ = _ := by
      rw [Real.sqrt_eq_rpow,Real.sqrt_eq_rpow,Real.rpow_add hN]
      ring

theorem standardKloosterman_weil_bound_primitive {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ) [NeZero N] (h k : ℤ),
      Nat.gcd N (Int.gcd h k)=1 → ‖standardSum N h k‖ ≤ C*(N:ℝ)^((1/2:ℝ)+ε) := by
  obtain ⟨C,hC,hbound⟩ := standardKloosterman_weil_bound hε
  refine ⟨C,hC,?_⟩
  intro N _inst h k hg
  simpa only [hg,Nat.cast_one,Real.one_rpow,mul_one] using hbound N h k

theorem unitKloostermanSum_weil_bound {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ) [NeZero N] (h k : ZMod N),
      ‖unitKloostermanSum N h k‖ ≤ C*(N:ℝ)^((1/2:ℝ)+ε)*
        ((Nat.gcd N (Nat.gcd h.val k.val):ℕ):ℝ)^(1/2:ℝ) := by
  obtain ⟨C,hC,hbound⟩ := standardKloosterman_weil_bound hε
  refine ⟨C,hC,?_⟩
  intro N _inst h k
  rw [unitKloostermanSum_eq_standardSum]
  simpa only [Int.gcd_def,Int.natAbs_natCast] using hbound N (h.val:ℤ) (k.val:ℤ)

theorem unitKloostermanSum_weil_bound_primitive {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ) [NeZero N] (h k : ZMod N),
      Nat.gcd N (Nat.gcd h.val k.val)=1 → ‖unitKloostermanSum N h k‖ ≤ C*(N:ℝ)^((1/2:ℝ)+ε) := by
  obtain ⟨C,hC,hbound⟩ := unitKloostermanSum_weil_bound hε
  refine ⟨C,hC,?_⟩
  intro N _inst h k hg
  simpa only [hg,Nat.cast_one,Real.one_rpow,mul_one] using hbound N h k

end ArtinMatthews
