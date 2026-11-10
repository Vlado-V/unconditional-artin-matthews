module

public import ArtinMatthews.MarkedMemoryTiltPrimewiseActual
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


set_option backward.privateInPublic true
@[expose] public section

/-! The literal finite independent projective-line expectation for an
active path. Its factorization and baseline extraction retain all active
coherence conditions and all inactive damping factors. No root average
is replaced, and no physical measure is identified with the tilted one. -/
namespace ArtinMatthews
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.decEq Classical.propDecidable

abbrev MarkedMemoryIndependentLines (S : Finset Nat.Primes) :=
  (p : S) → MarkedRawPrimeLine p.1

instance markedMemoryIndependentLines_fintype (S : Finset Nat.Primes) :
    Fintype (MarkedMemoryIndependentLines S) := by infer_instance

variable {J : Type*} [Fintype J] {P : J → Finset Nat.Primes} {M N : ℕ}
  (S : Finset Nat.Primes) (slots : Fin (N+1) → MarkedRawActive P M)
  (q : ℝ) (z : Fin (N+1) → ℤ × ℤ) (hz : ∀ v,IsCoprime (z v).1 (z v).2)

def markedMemoryPathLineFactor (p : S) (ell : MarkedRawPrimeLine p.1) : ℝ :=
  (∏ v ∈ markedMemoryActiveVisits slots p.1,
    markedLineHit (markedMemoryPositionLines p.1 z hz) v ell) *
  ∏ v ∈ Finset.univ \ markedMemoryActiveVisits slots p.1,
    (1-markedMemoryEta q N v*markedLineHit (markedMemoryPositionLines p.1 z hz) v ell)

def markedMemoryIndependentLineExpectation : ℝ :=
  (∑ ell : MarkedMemoryIndependentLines S,∏ p : S,markedMemoryPathLineFactor S slots q z hz p (ell p)) /
    (Fintype.card (MarkedMemoryIndependentLines S) : ℝ)

theorem markedMemoryIndependentLineExpectation_factorization :
    markedMemoryIndependentLineExpectation S slots q z hz=
      ∏ p : S,markedMemoryProjectiveFactor p.1 q z hz (markedMemoryActiveVisits slots p.1) := by
  unfold markedMemoryIndependentLineExpectation
  rw [← Fintype.prod_sum (fun p : S => markedMemoryPathLineFactor S slots q z hz p)]
  rw [Fintype.card_pi,Nat.cast_prod,← Finset.prod_div_distrib]
  apply Finset.prod_congr rfl
  intro p _
  rfl

theorem markedMemoryIndependentLineExpectation_baseline
    (hb : ∀ p : S,markedMemoryBaseline q N p.1≠0) :
    markedMemoryIndependentLineExpectation S slots q z hz=
      (∏ p : S,markedMemoryBaseline q N p.1) *
        ∏ p : S,markedMemoryProjectiveFactor p.1 q z hz (markedMemoryActiveVisits slots p.1) /
          markedMemoryBaseline q N p.1 := by
  rw [markedMemoryIndependentLineExpectation_factorization,← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro p _
  field_simp [hb p]

theorem markedMemoryIndependentLines_card :
    Fintype.card (MarkedMemoryIndependentLines S)=∏ p : S,((p.1:ℕ)+1) := by
  rw [Fintype.card_pi]
  apply Finset.prod_congr rfl
  intro p _
  exact markedMemoryPrimeLine_card p.1

end
end ArtinMatthews
