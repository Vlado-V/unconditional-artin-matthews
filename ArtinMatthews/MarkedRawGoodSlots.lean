module

public import ArtinMatthews.MarkedMinorArcDirtyGoodCutoff
public import ArtinMatthews.MarkedRawGoodRootMeasure
public import ArtinMatthews.MarkedMinorArcDirtyPermutationAction
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

/-! Both actual good tests are invariant under active-slot permutations.
The dyadic omission family is reindexed exactly, including its cap. -/
namespace ArtinMatthews
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem markedRawCopiedProduct_slots {J : Type*} [Fintype J]
    {P : J → Finset Nat.Primes} {M : ℕ} (a : MarkedRawActive P M)
    (σ : J → Equiv.Perm (Fin M)) (o : J → Fin M) :
    markedSourceCopiedProduct (markedRawNumericActive (markedRawActiveSlotEquiv σ a)) o =
      markedSourceCopiedProduct (markedRawNumericActive a) (fun j => σ j (o j)) :=
  markedSourceCopiedProduct_permuted (markedRawNumericActive a) σ o

def markedRawDyadicOmissionSlotEquiv {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} {M : ℕ} (a : MarkedRawActive P M) (d₀ : ℝ)
    (σ : J → Equiv.Perm (Fin M)) :
    markedRawDyadicOmissions (markedRawActiveSlotEquiv σ a) d₀ ≃ markedRawDyadicOmissions a d₀ where
  toFun o := ⟨fun j => σ j (o.1 j),by
    have h := (Finset.mem_filter.mp o.2).2
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _,?_⟩
    rwa [markedRawCopiedProduct_slots] at h⟩
  invFun o := ⟨fun j => (σ j).symm (o.1 j),by
    have h := (Finset.mem_filter.mp o.2).2
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _,?_⟩
    rw [markedRawCopiedProduct_slots]
    simpa only [Equiv.apply_symm_apply] using h⟩
  left_inv o := by apply Subtype.ext; funext j; exact (σ j).symm_apply_apply (o.1 j)
  right_inv o := by apply Subtype.ext; funext j; exact (σ j).apply_symm_apply (o.1 j)

theorem markedRawFirstBadRootSet_slots {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} {M : ℕ} (a : MarkedRawActive P M) (d₀ Y : ℝ)
    (σ : J → Equiv.Perm (Fin M)) :
    markedRawFirstBadRootSet (markedRawActiveSlotEquiv σ a) d₀ Y = markedRawFirstBadRootSet a d₀ Y := by
  let E := markedRawDyadicOmissionSlotEquiv a d₀ σ
  unfold markedRawFirstBadRootSet markedFirstBadRoots
  have hprod (o : markedRawDyadicOmissions (markedRawActiveSlotEquiv σ a) d₀) :
      markedSourceCopiedProduct (markedRawNumericActive (markedRawActiveSlotEquiv σ a)) o.1 =
        markedSourceCopiedProduct (markedRawNumericActive a) (E o).1 :=
    markedRawCopiedProduct_slots a σ o.1
  simp_rw [hprod]
  exact E.surjective.iUnion_comp (fun i : markedRawDyadicOmissions a d₀ =>
    ⋃ l ∈ Finset.Icc 1 ⌊Y^(1/5:ℝ)⌋₊,
      markedBadRootMultiple ((markedSourceCopiedProduct (markedRawNumericActive a) i.1*l:ℕ):ℤ)
        (Y^(-7/10:ℝ)))

theorem markedRawFirstGood_slots {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} {M B : ℕ} {Z : Finset (ℤ × ℤ)}
    (r d₀ Y : ℝ) (w : Z → ℤ × ℤ) (s : MarkedRawState P M B Z)
    (σ : J → Equiv.Perm (Fin M)) :
    MarkedRawFirstGood r d₀ Y w (markedRawSlotEquiv σ s) ↔ MarkedRawFirstGood r d₀ Y w s := by
  change _ ∉ markedRawFirstBadRootSet (markedRawActiveSlotEquiv σ s.2.1) d₀ Y ↔
    _ ∉ markedRawFirstBadRootSet s.2.1 d₀ Y
  rw [markedRawFirstBadRootSet_slots]
  rfl

theorem markedRawDirtyGood_slots {J : Type*} [Fintype J] [DecidableEq J]
    (e : J → ℝ) (x r d₀ Y : ℝ) {M B : ℕ} {Z : Finset (ℤ × ℤ)}
    (w : Z → ℤ × ℤ) (s : MarkedRawState (markedRawActualPrimeBand e x) M B Z)
    (σ : J → Equiv.Perm (Fin M)) :
    MarkedRawDirtyGood e x r d₀ Y w (markedRawSlotEquiv σ s) ↔ MarkedRawDirtyGood e x r d₀ Y w s := by
  exact and_congr (markedRawFirstGood_slots r d₀ Y w s σ) (markedRawDirtySecondGood_slots e x r w s σ)

end
end ArtinMatthews
