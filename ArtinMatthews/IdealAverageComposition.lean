module

public import ArtinMatthews.IdealProductAverage
public import ArtinMatthews.IdealHarmonicComponents
public import ArtinMatthews.IdealProbeAverages
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

/-! Coordinate averages commute and compose on the full original
harmonic product law. -/
namespace ArtinMatthews
open Finset
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

theorem idealAverageSet_union {G : Type*} [Fintype G] [DecidableEq G]
    (P : G → Finset ℕ) {M : ℕ} (hV : ∀ g,0 < bandReciprocalMass (P g))
    (hP : ∀ g p,p∈P g → 0 < p) (S T : Finset (G × Fin M))
    (f : MarkedPhysicalMarking P M → ℂ) :
    idealAverageSet P S (idealAverageSet P T f)=idealAverageSet P (T ∪ S) f := by
  obtain ⟨a₀,b,hb⟩ := idealHarmonicBasis_exists P hV hP
  have he := idealAverageSet_probeProjection P hV
    (fun g p => idealHarmonicAtom_pos (P g) (hV g) (hP g) p) b a₀ hb S ∅ T f
  have hempty (U : Finset (G × Fin M)) :
      idealProbeProjection P ∅ U f=idealAverageSet P U f := by
    funext a
    unfold idealProbeProjection
    rw [powerset_empty,sum_singleton]
    simp only [card_empty,pow_zero,union_empty,one_mul]
  rw [hempty T,hempty (T ∪ S)] at he
  exact he

theorem idealAverageSet_subset_left {G : Type*} [Fintype G] [DecidableEq G]
    (P : G → Finset ℕ) {M : ℕ} (hV : ∀ g,0 < bandReciprocalMass (P g))
    (hP : ∀ g p,p∈P g → 0 < p) (S T : Finset (G × Fin M)) (hST : S ⊆ T)
    (f : MarkedPhysicalMarking P M → ℂ) :
    idealAverageSet P T (idealAverageSet P S f)=idealAverageSet P T f := by
  rw [idealAverageSet_union P hV hP,union_eq_right.mpr hST]

theorem idealAverageSet_of_independent {G : Type*} [Fintype G] [DecidableEq G]
    (P : G → Finset ℕ) {M : ℕ} (hV : ∀ g,0 < bandReciprocalMass (P g))
    (S : Finset (G × Fin M)) (f : MarkedPhysicalMarking P M → ℂ)
    (hf : ∀ a b,f (idealMix S a b)=f a) : idealAverageSet P S f=f := by
  funext a
  unfold idealAverageSet idealLabelExpectation
  simp_rw [hf]
  rw [← sum_mul,← map_sum,idealLabelMass_sum P M hV,map_one,one_mul]

end
end ArtinMatthews
