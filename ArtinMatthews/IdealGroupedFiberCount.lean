module

public import ArtinMatthews.IdealGroupedProducts
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Nat.Factorial.Basic
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

/-! Each numeric-product fiber is contained in the actual per-group
permutation family. Repeated labels reduce its size. -/
namespace ArtinMatthews
open Finset
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

variable {J : Type*} [Fintype J] [DecidableEq J]

abbrev IdealGroupedFiber (P : J → Finset ℕ) (k : J → ℕ) (n : ℕ) :=
  {a : IdealGroupedLabels P k // idealGroupedProduct a = n}

def idealGroupedFiberWords {P : J → Finset ℕ} {k : J → ℕ}
    (hP : ∀ j p, p ∈ P j → p.Prime)
    (hdis : Pairwise (fun j l => Disjoint (P j) (P l)))
    (a : IdealGroupedLabels P k)
    (b : IdealGroupedFiber P k (idealGroupedProduct a)) :
    ∀ j, ↥((idealGroupWord a j).permutations.toFinset) := fun j =>
  ⟨idealGroupWord b.val j, List.mem_toFinset.mpr (List.mem_permutations.mpr
    (idealGroupedProduct_word_perm hP hdis b.val a b.property j))⟩

theorem idealGroupedFiberWords_injective {P : J → Finset ℕ} {k : J → ℕ}
    (hP : ∀ j p, p ∈ P j → p.Prime)
    (hdis : Pairwise (fun j l => Disjoint (P j) (P l))) (a : IdealGroupedLabels P k) :
    Function.Injective (idealGroupedFiberWords hP hdis a) := by
  intro b c he
  apply Subtype.ext
  funext j i
  apply Subtype.ext
  have hl : idealGroupWord b.val j = idealGroupWord c.val j :=
    congrArg Subtype.val (congrFun he j)
  exact congrFun (List.ofFn_injective hl) i

theorem idealGroupedProduct_fiber_card_le {P : J → Finset ℕ} {k : J → ℕ}
    (hP : ∀ j p, p ∈ P j → p.Prime)
    (hdis : Pairwise (fun j l => Disjoint (P j) (P l))) (n : ℕ) :
    Fintype.card (IdealGroupedFiber P k n) ≤ ∏ j, (k j).factorial := by
  by_cases hne : Nonempty (IdealGroupedFiber P k n)
  · obtain ⟨a⟩ := hne
    have hn : n = idealGroupedProduct a.val := a.property.symm
    rw [hn]
    calc
      _ ≤ Fintype.card (∀ j, ↥((idealGroupWord a.val j).permutations.toFinset)) :=
        Fintype.card_le_of_injective _ (idealGroupedFiberWords_injective hP hdis a.val)
      _ = ∏ j, ((idealGroupWord a.val j).permutations.toFinset).card := by simp
      _ ≤ ∏ j, (k j).factorial := by
        apply prod_le_prod
        intro j _
        calc
          _ ≤ ((idealGroupWord a.val j).permutations).length := List.toFinset_card_le _
          _ = (k j).factorial := by rw [List.length_permutations]; simp [idealGroupWord]
  · let : IsEmpty (IdealGroupedFiber P k n) := ⟨fun a => hne ⟨a⟩⟩
    simp only [Fintype.card_of_isEmpty]
    exact Nat.zero_le _

end
end ArtinMatthews
