module

public import ArtinMatthews.GiantSignedBirthPivots
public import ArtinMatthews.GiantSignedBirthTypedBand
public import ArtinMatthews.MarkedInjectedBirthMass
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

/-! Extend the retained prime memo by precisely the performed local
draws, leaving absent addresses unchanged. -/
namespace ArtinMatthews
noncomputable section
attribute [local instance] Classical.propDecidable Classical.decEq

variable {B I : Type*} {M n H : ℕ} [Fintype I]
    {PB : B → Finset ℕ} (hPB : ∀ g p, p ∈ PB g → p.Prime)

def giantSignedUniformBirthConditionalValues
    (e : I ↪ GiantSignedUniformBirthAddress B M n H)
    (old : GiantSignedUniformBirthAddress B M n H → Option Nat.Primes)
    (t : (i : I) → PB (giantSignedUniformBirthGroup (e i))) :
    GiantSignedUniformBirthAddress B M n H → Option Nat.Primes :=
  let P (a : GiantSignedUniformBirthAddress B M n H) :=
    giantSignedTypedPrimeBand (PB (giantSignedUniformBirthGroup a)) (hPB (giantSignedUniformBirthGroup a))
  markedConditionalBirthValues (P := P) old (markedBirthDrawSet e)
    (markedBirthDrawTupleEquiv P e e.injective (fun i =>
      giantSignedTypedPrimeBandEquiv (PB (giantSignedUniformBirthGroup (e i)))
        (hPB (giantSignedUniformBirthGroup (e i))) (t i)))

theorem giantSignedUniformBirthConditionalValues_draw
    (e : I ↪ GiantSignedUniformBirthAddress B M n H)
    (old : GiantSignedUniformBirthAddress B M n H → Option Nat.Primes)
    (t : (i : I) → PB (giantSignedUniformBirthGroup (e i))) (i : I) :
    giantSignedUniformBirthConditionalValues hPB e old t (e i) =
      some (⟨(t i).val,hPB (giantSignedUniformBirthGroup (e i)) (t i).val (t i).property⟩ : Nat.Primes) := by
  unfold giantSignedUniformBirthConditionalValues
  dsimp only
  rw [markedBirthDrawValues_apply, giantSignedTypedPrimeBandEquiv_value] <;> rfl

theorem giantSignedUniformBirthConditionalValues_outside
    (e : I ↪ GiantSignedUniformBirthAddress B M n H)
    (old : GiantSignedUniformBirthAddress B M n H → Option Nat.Primes)
    (t : (i : I) → PB (giantSignedUniformBirthGroup (e i)))
    (a : GiantSignedUniformBirthAddress B M n H) (ha : a ∉ Set.range e) :
    giantSignedUniformBirthConditionalValues hPB e old t a = old a := by
  have hdraw : a ∉ markedBirthDrawSet e := by
    intro h
    obtain ⟨i,hi⟩ := (markedBirthDrawEquiv e e.injective).surjective ⟨a,h⟩
    exact ha ⟨i,congrArg Subtype.val hi⟩
  unfold giantSignedUniformBirthConditionalValues markedConditionalBirthValues
  rw [dite_eq_right hdraw]

def GiantSignedUniformBirthConditionalGate [Fintype B]
    (σ : Equiv.Perm (GiantSignedUniformBirthAddress B M n H)) (o : GiantSignedBirthOperation n)
    (values : GiantSignedUniformBirthAddress B M n H → Option Nat.Primes) : Prop :=
  ∀ a ∈ giantSignedUniformBirthStageNonpivots σ o,
    values a ≠ none ∧ values a = values (giantSignedUniformBirthPivot σ a)

end
end ArtinMatthews
