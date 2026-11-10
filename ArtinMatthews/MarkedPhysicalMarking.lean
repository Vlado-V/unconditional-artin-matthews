module

public import ArtinMatthews.MarkedMinorArcRawPrimeBands
public import ArtinMatthews.MarkedMinorArcRawCleanKernel
public import ArtinMatthews.MarkedArrayExpansion
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
public import Mathlib.RingTheory.WittVector.IsPoly
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
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! Literal ordered physical markings from PD03. These use counting measure
times `∏ Vᵢ⁻ᴹ`, before the signed-memory change of measure. No ordering or
factorial multiplicity is discarded by the adapters below. -/
noncomputable section
open scoped BigOperators
namespace ArtinMatthews
attribute [local instance] Classical.propDecidable

abbrev MarkedPhysicalMarking {J : Type*} (P : J → Finset ℕ) (M : ℕ) :=
  (j : J) → Fin M → ↥(P j)

def markedPhysicalMarkingEquiv {J : Type*} (P : J → Finset ℕ)
    (hP : ∀ j p, p ∈ P j → p.Prime) (M : ℕ) :
    MarkedRawActive (fun j => markedRawPrimeBand (P j)) M ≃ MarkedPhysicalMarking P M :=
  Equiv.piCongrRight (fun j => Equiv.piCongrRight (fun _ => markedRawPrimeBandEquiv (P j) (hP j)))

@[simp] theorem markedPhysicalMarkingEquiv_apply {J : Type*} (P : J → Finset ℕ)
    (hP : ∀ j p, p ∈ P j → p.Prime) (M : ℕ)
    (a : MarkedRawActive (fun j => markedRawPrimeBand (P j)) M) (j : J) (k : Fin M) :
    ((markedPhysicalMarkingEquiv P hP M a j k : ↥(P j)) : ℕ) = (a j k).1.1 := rfl

def markedPhysicalMarkingArrayEquiv {J : Type*} [Fintype J]
    (P : J → Finset ℕ) (M : ℕ) :
    MarkedPhysicalMarking P M ≃ ↥(representedArrayChoices P (fun _ => M)) where
  toFun a := ⟨fun j k => a j k, by
    classical
    simp only [representedArrayChoices, Fintype.mem_piFinset]
    exact fun j k => (a j k).2⟩
  invFun a j k := ⟨a.1 j k, by
    have h := a.2
    simp only [representedArrayChoices, Fintype.mem_piFinset] at h
    exact h j k⟩
  left_inv _ := rfl
  right_inv _ := rfl

def MarkedPhysicalMarkingDistinct {J : Type*} {P : J → Finset ℕ} {M : ℕ}
    (a : MarkedPhysicalMarking P M) : Prop := ∀ j, Function.Injective (a j)

theorem markedPhysicalMarkingEquiv_distinct {J : Type*} (P : J → Finset ℕ)
    (hP : ∀ j p, p ∈ P j → p.Prime) (M : ℕ)
    (a : MarkedRawActive (fun j => markedRawPrimeBand (P j)) M) :
    MarkedPhysicalMarkingDistinct (markedPhysicalMarkingEquiv P hP M a) ↔
      MarkedRawActiveDistinct a := by
  constructor
  · intro h j k l hkl
    apply h j
    exact congrArg (markedRawPrimeBandEquiv (P j) (hP j)) hkl
  · intro h j k l hkl
    apply h j
    exact (markedRawPrimeBandEquiv (P j) (hP j)).injective hkl

def markedPhysicalMass {J : Type*} [Fintype J] (V : J → ℝ) (M : ℕ) : ℝ :=
  ∏ j, (V j)⁻¹ ^ M

def markedPhysicalMarkingProduct {J : Type*} [Fintype J] {P : J → Finset ℕ} {M : ℕ}
    (a : MarkedPhysicalMarking P M) : ℕ := ∏ j, ∏ k, (a j k : ℕ)

def markedPhysicalReciprocalProduct {J : Type*} [Fintype J] {P : J → Finset ℕ} {M : ℕ}
    (a : MarkedPhysicalMarking P M) : ℝ := ∏ j, ∏ k, (1 / (a j k : ℝ))

theorem markedPhysicalReciprocalProduct_eq {J : Type*} [Fintype J]
    {P : J → Finset ℕ} {M : ℕ} (a : MarkedPhysicalMarking P M) :
    markedPhysicalReciprocalProduct a = 1 / (markedPhysicalMarkingProduct a : ℝ) := by
  simp [markedPhysicalReciprocalProduct, markedPhysicalMarkingProduct,
    Finset.prod_inv_distrib, Nat.cast_prod]

theorem markedPhysicalMass_eq_rawActiveMass {J : Type*} [Fintype J]
    (P : J → Finset Nat.Primes) (V : J → ℝ) (M : ℕ) (a : MarkedRawActive P M) :
    markedPhysicalMass V M = markedRawActiveMass (fun j _ => (V j)⁻¹) a := by
  simp [markedPhysicalMass, markedRawActiveMass]

/-- The physical normalization times the literal reciprocal product is the
ordered harmonic product mass. This is an identity, not a replacement of
the original physical measure by the later tilted raw-memory measure. -/
theorem markedPhysicalMass_mul_reciprocal {J : Type*} [Fintype J]
    (P : J → Finset ℕ) (M : ℕ) (a : MarkedPhysicalMarking P M) :
    markedPhysicalMass (fun j => bandReciprocalMass (P j)) M *
      markedPhysicalReciprocalProduct a =
      ∏ j, ∏ k, markedHarmonicAtom (P j) (a j k) := by
  simp only [markedPhysicalMass, markedPhysicalReciprocalProduct,
    ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro j _
  rw [show (bandReciprocalMass (P j))⁻¹ ^ M =
    ∏ _k : Fin M, (bandReciprocalMass (P j))⁻¹ by simp,
    ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro k _
  simp [markedHarmonicAtom, div_eq_mul_inv, mul_comm]

theorem markedPhysicalMarking_normalized_sum {J : Type*} [Fintype J] [DecidableEq J]
    (P : J → Finset ℕ) (M : ℕ) (hV : ∀ j, 0 < bandReciprocalMass (P j)) :
    (∑ a : MarkedPhysicalMarking P M,
      markedPhysicalMass (fun j => bandReciprocalMass (P j)) M *
        markedPhysicalReciprocalProduct a) = 1 := by
  simp_rw [markedPhysicalMass_mul_reciprocal]
  rw [← Fintype.prod_sum (fun j (b : Fin M → ↥(P j)) =>
    ∏ k, markedHarmonicAtom (P j) (b k))]
  have hj (j : J) : (∑ b : Fin M → ↥(P j), ∏ k, markedHarmonicAtom (P j) (b k)) = 1 := by
    rw [← Fintype.prod_sum (fun (_k : Fin M) (p : ↥(P j)) => markedHarmonicAtom (P j) p)]
    simp_rw [markedHarmonicAtom_sum (P j) (hV j)]
    simp
  simp_rw [hj]
  simp

/-- Exactly the normalized distinct-list reciprocal sum in PD03 after
`det:endpoint-norms`. Ordered label multiplicities are retained. -/
theorem markedPhysicalMarking_distinct_normalized_sum_le_one {J : Type*} [Fintype J] [DecidableEq J]
    (P : J → Finset ℕ) (M : ℕ) (hV : ∀ j, 0 < bandReciprocalMass (P j)) :
    (∑ a : MarkedPhysicalMarking P M,
      if MarkedPhysicalMarkingDistinct a then
        markedPhysicalMass (fun j => bandReciprocalMass (P j)) M *
          markedPhysicalReciprocalProduct a else 0) ≤ 1 := by
  classical
  rw [← markedPhysicalMarking_normalized_sum P M hV]
  apply Finset.sum_le_sum
  intro a _
  split_ifs
  · exact le_rfl
  · rw [markedPhysicalMass_mul_reciprocal]
    exact Finset.prod_nonneg (fun j _ => Finset.prod_nonneg
      (fun _ _ => markedHarmonicAtom_nonneg (P j) (hV j)))

end ArtinMatthews
