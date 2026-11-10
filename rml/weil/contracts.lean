module

public import rml.weil.crt_and_completion
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
public import rml.weil.prime_kloosterman

@[expose] public section

/-!
# Unconditional bounds derived from the prime theorem

The underlying general lemmas in `rml.weil.crt_and_completion` accept a
`PrimeNondegenerateWeil` proof explicitly. Here they are instantiated with
`prime_bound`; callers do not need to supply that argument.
-/

namespace RML.ExpSum.Weil

/-- Squarefree-modulus estimate for a unit numerator. -/
theorem squarefreeUnitNumerator_bound
    {q : ℕ} [NeZero q] (hsq : Squarefree q)
    (a b : ZMod q) (ha : IsUnit a) :
    ‖kloostermanUnitSum q a b‖ ≤
      (2 : ℝ) ^ q.primeFactors.card * Real.sqrt q :=
  kloostermanUnitSum_squarefree_unit_le prime_bound hsq a b ha

/-- Bound on the sum at the reduced modulus, with no lifting assertion. -/
theorem reducedModulusSum_bound
    {A q : ℕ} (hq : 0 < q) (hsq : Squarefree q)
    (b : ZMod (reducedModulus A q)) :
    letI : NeZero (reducedModulus A q) :=
      ⟨Nat.ne_of_gt (reducedModulus_pos hq)⟩
    ‖kloostermanUnitSum (reducedModulus A q)
       (reducedNumerator A q : ZMod (reducedModulus A q)) b‖ ≤
       (2 : ℝ) ^ (reducedModulus A q).primeFactors.card *
       Real.sqrt (reducedModulus A q) :=
  kloostermanUnitSum_reduced_le prime_bound hq hsq b

/-- Centered completion on the reduced squarefree modulus. -/
theorem centeredReducedIntervalSum_bound
    {A q : ℕ} (hq : 0 < q) (hsq : Squarefree q)
    (x : ZMod (reducedModulus A q)) (L : ℕ) :
    letI : NeZero (reducedModulus A q) :=
      ⟨Nat.ne_of_gt (reducedModulus_pos hq)⟩
    ‖centeredIntervalSum
        (reducedModulus A q)
        (reducedNumerator A q : ZMod (reducedModulus A q))
        x L‖ ≤
      ((2 : ℝ) ^ (reducedModulus A q).primeFactors.card *
          Real.sqrt (reducedModulus A q)) *
        (1 + Real.log (reducedModulus A q)) :=
  centeredReducedIntervalSum_le prime_bound hq hsq x L

/-- Weighted centered completion with positive initial weight `Y`. -/
theorem weightedCenteredReducedIntervalSum_bound
    {A q : ℕ} (hq : 0 < q) (hsq : Squarefree q)
    (x : ZMod (reducedModulus A q))
    (Y L : ℕ) (hY : 0 < Y) :
    letI : NeZero (reducedModulus A q) :=
      ⟨Nat.ne_of_gt (reducedModulus_pos hq)⟩
    ‖weightedCenteredIntervalSum
        (reducedModulus A q)
        (reducedNumerator A q : ZMod (reducedModulus A q))
        x Y L‖ ≤
      2 *
        (((2 : ℝ) ^ (reducedModulus A q).primeFactors.card *
            Real.sqrt (reducedModulus A q)) *
          (1 + Real.log (reducedModulus A q))) / Y :=
  weightedCenteredReducedIntervalSum_le prime_bound hq hsq x Y L hY

end RML.ExpSum.Weil
