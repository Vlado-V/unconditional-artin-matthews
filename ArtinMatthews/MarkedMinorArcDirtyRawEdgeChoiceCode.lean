module

public import ArtinMatthews.MarkedMinorArcDirtyRawEdgeFresh
public import ArtinMatthews.MarkedMinorArcRawSlotAverage
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

/-! Actual edge choices retain no hidden fresh labels in promoted groups,
and their finite index space is independent of source slot ordering. -/
noncomputable section
namespace ArtinMatthews

def markedDirtyRawEdgeChoiceReducedCode {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (s : MarkedRawState P (pads+1) B Z)
    (choice : MarkedRawEdgeChoice hZ s) :
    Z × ((J → Bool) × (Σ prom : MarkedRawEdgePromotions s.2.2,
      (j : markedDirtyEdgeFreshGroups prom) → ↥(P j.1))) :=
  (choice.target,(choice.store,⟨choice.promotions,markedDirtyEdgeFreshTuple s.2.2 choice.promotions choice.fresh⟩))

theorem markedDirtyRawEdgeChoiceReducedCode_injective {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (s : MarkedRawState P (pads+1) B Z) :
    Function.Injective (markedDirtyRawEdgeChoiceReducedCode hZ s) := by
  rintro ⟨ta,sa,pa,fa,hpa,hba⟩ ⟨tb,sb,pb,fb,hpb,hbb⟩ he
  change (ta,(sa,(Sigma.mk pa (markedDirtyEdgeFreshTuple s.2.2 pa fa) :
      Σ prom : MarkedRawEdgePromotions s.2.2, (j : markedDirtyEdgeFreshGroups prom) → ↥(P j.1))))=
    (tb,(sb,Sigma.mk pb (markedDirtyEdgeFreshTuple s.2.2 pb fb))) at he
  have ht := congrArg Prod.fst he
  cases ht
  have hp := congrArg Prod.snd he
  have hs := congrArg Prod.fst hp
  cases hs
  have hsig := congrArg Prod.snd hp
  have hprom := congrArg Sigma.fst hsig
  cases hprom
  have hf : markedDirtyEdgeFreshTuple s.2.2 pa fa=markedDirtyEdgeFreshTuple s.2.2 pa fb :=
    eq_of_heq (Sigma.mk.inj_iff.mp hsig).2
  have heq := markedDirtyEdgeFreshTuple_injective s.2.2 pa hf
  cases heq
  rfl

/-- Active source slot permutations preserve every literal edge-choice
coordinate and every admissibility constraint. They change actual source
labels and copied products, but do not create extra index multiplicity. -/
def markedDirtyRawEdgeChoiceSlotEquiv {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (s : MarkedRawState P (pads+1) B Z)
    (σ : J → Equiv.Perm (Fin (pads+1))) :
    MarkedRawEdgeChoice hZ (markedRawSlotEquiv σ s) ≃ MarkedRawEdgeChoice hZ s where
  toFun c := ⟨c.target,c.store,c.promotions,c.fresh,c.promotion_hits,c.memory_bound⟩
  invFun c := ⟨c.target,c.store,c.promotions,c.fresh,c.promotion_hits,c.memory_bound⟩
  left_inv c := by cases c; rfl
  right_inv c := by cases c; rfl

end ArtinMatthews
