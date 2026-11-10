module

public import ArtinMatthews.MarkedMinorArcRawPrimeBands
public import ArtinMatthews.MarkedMinorArcRawCleanKernel
public import ArtinMatthews.MarkedEstimateActualModel
public import ArtinMatthews.MarkedMinorArcRawProducts
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

/-! Exact product transport of the actual raw last-label measure. The prime
labels remain the genuine growing PD bands and their literal tilted atoms. -/
namespace ArtinMatthews
open Filter
open scoped BigOperators

/-- The literal last-label tuple in the original natural prime bands. -/
noncomputable def markedRawActualNaturalLast {J : Type*} (e : J → ℝ) (x : ℝ)
    (last : (j : J) → ↥(markedRawActualPrimeBand e x j)) :
    (j : J) → ↥(markedLogPowerBand (e j) x) := fun j =>
  markedRawPrimeBandEquiv _ (fun _ hp => (mem_markedLogPowerBand.mp hp).1) (last j)

/-- Passing to prime-typed states changes no numeric product. -/
theorem markedRawActualNaturalLast_product {J : Type*} [Fintype J] (e : J → ℝ) (x : ℝ)
    (last : (j : J) → ↥(markedRawActualPrimeBand e x j)) :
    markedPrimeBandProduct (fun j => markedLogPowerBand (e j) x)
      (markedRawActualNaturalLast e x last)=markedRawLastProduct last := rfl

/-- Passing to prime-typed states changes no prime-product measure. -/
theorem markedRawActualLastMass_eq {J : Type*} [Fintype J] (e : J → ℝ) (q x : ℝ)
    (last : (j : J) → ↥(markedRawActualPrimeBand e x j)) :
    markedRawLastMass (markedRawActualPrimeAtom e q x) last=
      markedMemoryProductMass (fun j => bandReciprocalMass (markedLogPowerBand (e j) x))
        q (markedMemoryMomentLength x) (fun j => ((markedRawActualNaturalLast e x last j) : ℕ)) := rfl

/-- The actual band disjointness is preserved by the exact prime-typed adapter. -/
theorem markedRawActualPrimeBand_disjoint_eventually {J : Type*} [Fintype J]
    (e : J → ℝ) (hinj : Function.Injective e) :
    ∀ᶠ x : ℝ in atTop, Pairwise (fun i j =>
      Disjoint (markedRawActualPrimeBand e x i) (markedRawActualPrimeBand e x j)) := by
  filter_upwards [marked_array_disjoint_eventually e hinj] with x hx
  intro i j hij
  apply Finset.disjoint_left.mpr
  intro p hpi hpj
  exact Finset.disjoint_left.mp (hx hij)
    ((mem_markedRawPrimeBand _ _).mp hpi) ((mem_markedRawPrimeBand _ _).mp hpj)

/-- Every actual raw last-label atom equals the pushed integer-product atom.
The one-fiber property is proved from the actual disjoint growing bands. -/
theorem markedRawActualLastMass_eq_integerProduct_eventually {J : Type*} [Fintype J]
    (e : J → ℝ) (hinj : Function.Injective e) :
    ∀ᶠ x : ℝ in atTop, ∀ (q : ℝ) (last : (j : J) → ↥(markedRawActualPrimeBand e x j)),
      markedRawLastMass (markedRawActualPrimeAtom e q x) last=
        markedMinorIntegerProductMass e q x (markedRawLastProduct last : ℤ) := by
  filter_upwards [marked_array_disjoint_eventually e hinj] with x hx
  intro q last
  rw [markedMinorIntegerProductMass,ite_eq_left (Int.natCast_nonneg _),Int.toNat_natCast]
  unfold markedActualMemoryProductAtom
  rw [← markedRawActualNaturalLast_product e x last,
    markedMemoryProductAtom_at_product _ (fun _ _ hp => (mem_markedLogPowerBand.mp hp).1) hx]
  exact markedRawActualLastMass_eq e q x last

/-- Actual numeric-product transport is injective, so it loses no state or
prime-label multiplicity in the counting-space clean operator. -/
theorem markedRawActualProductMap_injective_eventually {J : Type*} [Fintype J] [DecidableEq J]
    (e : J → ℝ) (hinj : Function.Injective e) :
    ∀ᶠ x : ℝ in atTop, ∀ Z : Finset (ℤ × ℤ),
      Function.Injective (markedRawProductMap (P := markedRawActualPrimeBand e x) (Z := Z)) := by
  filter_upwards [markedRawActualPrimeBand_disjoint_eventually e hinj] with x hx
  intro Z
  exact markedRawProductMap_injective hx

end ArtinMatthews
