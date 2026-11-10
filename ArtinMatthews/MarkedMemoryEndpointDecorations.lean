module

public import ArtinMatthews.MarkedMemoryEndpointFamily
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

/-! Genuine global decomposition of every normalized finite tableau into
its bare endpoint family, ordered birth enumerations and copied-slot
orders. The inverse constructs the original local data, preserving all
literal decorations and tests. -/
namespace ArtinMatthews
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

variable {J : Type*} [Fintype J] [DecidableEq J] {A : J → Type*}
  [∀ j,Fintype (A j)] [∀ j,DecidableEq (A j)]
  {P : J → Finset Nat.Primes} {pads B n : ℕ} {Z : Finset (ℤ × ℤ)}
  (hZ : ∀ z ∈ Z,IsCoprime z.1 z.2) (s : MarkedRawState P (pads+1) B Z)
  (hempty : ∀ j,(s.2.2.1.1 j:ℕ)=0)

abbrev MarkedMemoryEndpointDecoratedIndex :=
  Σ e : MarkedMemoryEndpointFamily (A := A) (n := n) hZ s,
    MarkedMemoryEndpointBirthOrders e.1 × (Fin n → J → Equiv.Perm (Fin pads))

def markedMemoryEndpointDecorationsEquiv :
    MarkedMemoryNormalizedHistoryIndex (A := A) (n := n) hZ s ≃
      MarkedMemoryEndpointDecoratedIndex (A := A) (n := n) hZ s where
  toFun i := ⟨markedMemoryEndpointFamilyOfIndex hZ s hempty i,
    markedMemoryEndpointOriginalBirths hZ i.1.1.1,i.1.2⟩
  invFun e := markedMemoryEndpointFamilyIndex hZ s e.1 e.2.1 e.2.2
  left_inv i := by
    apply Subtype.ext
    apply Prod.ext
    · apply Subtype.ext
      apply Subtype.ext
      exact markedMemoryEndpointOriginal_rebuild hZ i.1.1.1
        (fun j => markedMemoryFiniteTableau_initial_empty hZ s i.1.1.1 i.1.1.2 hempty j)
    · rfl
  right_inv e := by
    rcases e with ⟨⟨d,hd⟩,births,order⟩
    cases d
    rfl

include hempty in
/-- Exact global reindexing keeps an arbitrary complete-history
functional attached to its reconstructed decorated family. -/
theorem markedMemoryEndpointDecorations_sum {R : Type*} [AddCommMonoid R]
    (F : MarkedMemoryNormalizedHistoryIndex (A := A) (n := n) hZ s → R) :
    (∑ i : MarkedMemoryNormalizedHistoryIndex (A := A) (n := n) hZ s,F i) =
      ∑ e : MarkedMemoryEndpointFamily (A := A) (n := n) hZ s,
        ∑ births : MarkedMemoryEndpointBirthOrders e.1,
          ∑ order : Fin n → J → Equiv.Perm (Fin pads),
            F (markedMemoryEndpointFamilyIndex hZ s e births order) := by
  rw [← Equiv.sum_comp (markedMemoryEndpointDecorationsEquiv hZ s hempty).symm]
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro e _
  exact Fintype.sum_prod_type _

theorem markedMemoryEndpointCopiedOrders_card :
    Fintype.card (Fin n → J → Equiv.Perm (Fin pads)) = (pads.factorial ^ Fintype.card J)^n := by
  simp only [Fintype.card_fun,Fintype.card_perm,Fintype.card_fin]

end
end ArtinMatthews
