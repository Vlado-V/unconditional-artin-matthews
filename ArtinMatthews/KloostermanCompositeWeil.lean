module

public import ArtinMatthews.KloostermanSqrtEnvelope
public import ArtinMatthews.KloostermanPrimePowerWeil
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.CStarAlgebra.Classes
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
public import OAI.NumberTheory.Jacobsthal.Sieve.KloostermanCRT


set_option backward.privateInPublic true
@[expose] public section

/-! Genuine CRT assembly of the square-root estimate at every nonzero modulus. -/
noncomputable section
open OAI.Erdos970.ErdosKloosterman
namespace ArtinMatthews.PrimePowerWeil

def SqrtBoundAt (N : ℕ) : Prop := ∀ [NeZero N] (h k : ℤ),
  ‖standardSum N h k‖ ≤ sqrtEnvelope N h k

theorem sqrtBoundAt_zero : SqrtBoundAt 0 := by
  intro h0 h k
  exact False.elim (NeZero.ne 0 rfl)

theorem sqrtBoundAt_one : SqrtBoundAt 1 := by
  intro _ h k
  simp [standardSum_one,sqrtEnvelope_one]

theorem sqrtBoundAt_coprime (m n : ℕ) (hm : 1 < m) (hn : 1 < n) (hmn : m.Coprime n)
    (hbm : SqrtBoundAt m) (hbn : SqrtBoundAt n) : SqrtBoundAt (m*n) := by
  let : NeZero m := ⟨by omega⟩
  let : NeZero n := ⟨by omega⟩
  intro _ h k
  rw [norm_standardSum_crt m n hmn]
  calc
    _ ≤ sqrtEnvelope m (Nat.gcdB m n*h) (Nat.gcdB m n*k)*
        sqrtEnvelope n (Nat.gcdA m n*h) (Nat.gcdA m n*k) :=
      mul_le_mul (hbm _ _) (hbn _ _) (norm_nonneg _) (sqrtEnvelope_nonneg _ _ _)
    _ = _ := sqrtEnvelope_crt_scaled m n hmn h k

theorem sqrtBoundAt_prime_power (p a : ℕ) (hp : p.Prime) (ha : 0 < a) : SqrtBoundAt (p^a) := by
  let : Fact p.Prime := ⟨hp⟩
  intro _ h k
  exact standardSum_prime_power_sqrtEnvelope p a ha h k

theorem sqrtBoundAt_all : ∀ N : ℕ, SqrtBoundAt N :=
  Nat.recOnPosPrimePosCoprime sqrtBoundAt_prime_power sqrtBoundAt_zero sqrtBoundAt_one sqrtBoundAt_coprime

theorem standardSum_weil_divisor_bound (N : ℕ) [NeZero N] (h k : ℤ) :
    ‖standardSum N h k‖ ≤ (N.divisors.card:ℝ)^3*Real.sqrt N*
      Real.sqrt ((Nat.gcd N (Int.gcd h k):ℕ):ℝ) :=
  sqrtBoundAt_all N h k

end ArtinMatthews.PrimePowerWeil
