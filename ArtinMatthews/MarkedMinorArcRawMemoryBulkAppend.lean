module

public import ArtinMatthews.MarkedMinorArcRawMemoryBulkSymmetry
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


set_option backward.privateInPublic true
@[expose] public section

/-! Normalizing actual old-deletion subset coordinates to fixed deleted and
surviving degrees, in the literal survivor-then-birth append order. -/
namespace ArtinMatthews
open scoped BigOperators

/-- The canonical reassembly is exactly the source ordered append, after
only the necessary degree equality cast. -/
theorem markedRawSubsetCanonicalTuple_append {X : Type*} {k : ℕ} (S : Finset (Fin k))
    (deleted : Fin S.card → X) (survivors : Fin (Sᶜ).card → X)
    (hk : (Sᶜ).card+S.card=k) :
    markedRawSubsetCanonicalTuple S deleted survivors=
      fun i => Fin.addCases survivors deleted (Fin.cast hk.symm i) := by
  have hcancel (a : Fin ((Sᶜ).card+S.card)) : Fin.cast hk.symm (Fin.cast hk a)=a := Fin.ext rfl
  funext i
  obtain ⟨a,rfl⟩ := (markedRawSubsetCanonicalIndex S).surjective i
  cases a with
  | inl d =>
    simp only [markedRawSubsetCanonicalTuple,Function.comp_apply,Equiv.symm_apply_apply,Sum.elim_inl]
    change deleted d=Fin.addCases survivors deleted
      (Fin.cast hk.symm (Fin.cast hk (Fin.natAdd (Sᶜ).card d)))
    simp only [hcancel,Fin.addCases_right]
  | inr r =>
    simp only [markedRawSubsetCanonicalTuple,Function.comp_apply,Equiv.symm_apply_apply,Sum.elim_inr]
    change survivors r=Fin.addCases survivors deleted
      (Fin.cast hk.symm (Fin.cast hk (Fin.castAdd S.card r)))
    simp only [hcancel,Fin.addCases_left]

/-- Deleted coordinates expressed in a fixed actual deleted degree. -/
def markedRawDeletedTupleCast {X : Type*} {k d : ℕ} (S : Finset (Fin k)) (hd : S.card=d)
    (a : Fin k → X) : Fin d → X :=
  fun i => (markedRawSubsetTupleEquiv S a).1 (Fin.cast hd.symm i)

/-- Surviving coordinates expressed in a fixed actual surviving degree. -/
def markedRawSurvivorTupleCast {X : Type*} {k n : ℕ} (S : Finset (Fin k)) (hn : (Sᶜ).card=n)
    (a : Fin k → X) : Fin n → X :=
  fun i => (markedRawSubsetTupleEquiv S a).2 (Fin.cast hn.symm i)

/-- Every actual old subset with the same deleted/surviving degrees has the
same finite symmetric-Fock integration formula. No conclusion of the ghost
operator or any row bound is supplied as an assumption. -/
theorem markedRawMemory_subset_fixed_degree_integral {X : Type*} [Fintype X]
    {k n d : ℕ} (hk : n+d=k) (S : Finset (Fin k)) (hd : S.card=d) (hn : (Sᶜ).card=n)
    (μ : X → ℂ) (g : (Fin k → X) → ℂ) (hg : MarkedRawTupleSymmetric k g)
    (f : (Fin d → X) → (Fin n → X) → ℂ) :
    (∑ a : Fin k → X, (∏ i, μ (a i))*g a*
      f (markedRawDeletedTupleCast S hd a) (markedRawSurvivorTupleCast S hn a))=
      ∑ deleted : Fin d → X, ∑ survivors : Fin n → X,
        (∏ i, μ (deleted i))*(∏ i, μ (survivors i))*
          g (fun i => Fin.addCases survivors deleted (Fin.cast hk.symm i))*f deleted survivors := by
  cases hd
  cases hn
  change (∑ a : Fin k → X, (∏ i, μ (a i))*g a*
    f (markedRawSubsetTupleEquiv S a).1 (markedRawSubsetTupleEquiv S a).2)=_
  simpa only [markedRawSubsetCanonicalTuple_append S _ _ hk] using
    markedRawMemory_subset_symmetric_integral S μ g hg f

end ArtinMatthews
