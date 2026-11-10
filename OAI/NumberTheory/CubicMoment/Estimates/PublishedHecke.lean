module

/- Adapted in the Artin–Matthews source bundle. The source, upstream and packaged digests are recorded in SOURCE_MANIFEST.json. -/

public import OAI.NumberTheory.CubicGram.SquarefreeGauss
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
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
public import Mathlib.Topology.Sheaves.Init
public import OAI.NumberTheory.CubicGram.Reciprocity


set_option backward.privateInPublic true
@[expose] public section

namespace OAI

/-!
# The finite-order Hecke prime input

The finite-order Hecke prime-sum input specializes to independent prime
factors using the elementary character laws.

The input is the cubic-character consequence of Thorner--Zaman,
*A unified and improved Chebotarev density theorem*, Algebra & Number
Theory 13 (2019), Theorem 1.4, in the Siegel–Walfisz form for cubic Hecke characters.  Only finite-order characters occur in this input;
smooth weights and norm twists follow by partial summation.
-/

noncomputable section
open scoped BigOperators
open Filter Asymptotics

namespace CubicFirstMoment

/-- The primitive cubic characters occurring after cancelling common
factors of two squarefree conductors. -/
def mixedCubic (q₁ q₂ a : Eisenstein) : ℂ :=
  cubicSymbol q₁ a * star (cubicSymbol q₂ a)

theorem mixedCubic_mul {q₁ q₂ : Eisenstein}
    (h₁ : primary q₁) (h₂ : primary q₂) (a b : Eisenstein) :
    mixedCubic q₁ q₂ (a * b) = mixedCubic q₁ q₂ a * mixedCubic q₁ q₂ b := by
  simp only [mixedCubic, cubicSymbol_mul_upper h₁, cubicSymbol_mul_upper h₂, star_mul]
  ring

theorem mixedCubic_one {q₁ q₂ : Eisenstein}
    (h₁ : primary q₁) (h₂ : primary q₂) : mixedCubic q₁ q₂ 1 = 1 := by
  rw [mixedCubic, cubic_reciprocity h₁ (by norm_num [primary]),
    cubic_reciprocity h₂ (by norm_num [primary]),
    cubicSymbol_one_lower, cubicSymbol_one_lower, star_one, mul_one]

theorem mixedCubic_norm_of_coprime {q₁ q₂ a : Eisenstein}
    (h₁ : primary q₁) (h₂ : primary q₂) (ha : IsCoprime (q₁ * q₂) a) :
    ‖mixedCubic q₁ q₂ a‖ = 1 := by
  rw [mixedCubic, norm_mul, norm_star,
    norm_cubicSymbol_of_isCoprime h₁ ha.of_mul_left_left,
    norm_cubicSymbol_of_isCoprime h₂ ha.of_mul_left_right, one_mul]

/-- Excludes the principal character on ideals prime to the conductor. -/
def MixedCubicNonprincipal (q₁ q₂ : Eisenstein) : Prop :=
  ∃ a : Eisenstein, primary a ∧ IsCoprime (q₁ * q₂) a ∧ mixedCubic q₁ q₂ a ≠ 1

/-- Exact logarithmic-conductor prime-sum input. The conductor is the
product of the coprime squarefree conductors of the two character factors.
Constants are uniform over that family. Both conjugate primes are counted.

This is an explicit hypothesis type, not an asserted theorem. -/
def CubicPrimeSiegelWalfisz : Prop :=
  ∀ A D : ℝ, 0 < A → 0 < D →
    ∃ C X₀ : ℝ, 0 < C ∧ 1 < X₀ ∧
      ∀ X : ℝ, X₀ ≤ X →
        ∀ q₁ q₂ : Eisenstein,
          primary q₁ → primary q₂ → Squarefree q₁ → Squarefree q₂ →
          IsCoprime q₁ q₂ → MixedCubicNonprincipal q₁ q₂ →
          norm (q₁ * q₂) ≤ (Real.log X) ^ A →
          ‖primeCutoffSum (mixedCubic q₁ q₂) X‖ ≤ C * X / (Real.log X) ^ D

/-- The character of an ordered tuple splits into the characters of its
individual factors. Repeated prime factors are still permitted here;
the squarefree restriction in the manuscript is imposed separately. -/
theorem mixedCubic_prod {ι : Type*} (s : Finset ι) (f : ι → Eisenstein)
    {q₁ q₂ : Eisenstein} (h₁ : primary q₁) (h₂ : primary q₂) :
    mixedCubic q₁ q₂ (∏ i ∈ s, f i) = ∏ i ∈ s, mixedCubic q₁ q₂ (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [mixedCubic_one h₁ h₂]
  | @insert i s hi ih => simp [hi, mixedCubic_mul h₁ h₂, ih]

/-- Exact factorization of an independent prime-tuple character sum.
The supports may be distinct smooth norm dyads, with their weights already
included in `w`. No condition coupling the tuple's product is inserted. -/
theorem independent_prime_tuple_character_sum {ι : Type*} [Fintype ι] [DecidableEq ι]
    (supports : ι → Finset Eisenstein) (w : ι → Eisenstein → ℂ)
    {q₁ q₂ : Eisenstein} (h₁ : primary q₁) (h₂ : primary q₂) :
    (∑ f ∈ Fintype.piFinset supports,
      (∏ i, w i (f i)) * mixedCubic q₁ q₂ (∏ i, f i)) =
      ∏ i, ∑ p ∈ supports i, w i p * mixedCubic q₁ q₂ p := by
  classical
  simp_rw [mixedCubic_prod _ _ h₁ h₂, ← Finset.prod_mul_distrib]
  exact (Finset.prod_univ_sum supports (fun i p => w i p * mixedCubic q₁ q₂ p)).symm

end CubicFirstMoment

end

end OAI
