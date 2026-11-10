module

public import ArtinMatthews.GiantSignedCleanDisintegration
public import ArtinMatthews.GiantSignedPairingEnergy
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

/-! The conditioned clean form is paired over the original full residue,
active-label and pending-memory measure, with no degree restriction. -/
namespace ArtinMatthews
open scoped BigOperators ENNReal
noncomputable section

variable {S B : Type*} [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B]
    (PS : S → Finset ℕ) {PB : B → Finset ℕ}
    [∀ p : ↥(markedPhysicalBandPrimes PS), NeZero p.val]

abbrev GiantSignedConditionedIndex (k ell : ℕ) :=
  MarkedPhysicalMarking PS k × (GiantSignedMemory PB ×
    (GiantTwoSidedFullResidue PS × MarkedPhysicalMarking PB (k+ell)))

def giantSignedConditionedWeight {k ell : ℕ} (ν : ∀ g, PB g → ℝ)
    (i : GiantSignedConditionedIndex PS (PB := PB) k ell) : ℝ :=
  giantSignedSmallHaar PS * giantSignedMemoryMass ν i.2.1 * giantSignedActiveMass ν i.2.2.2

def giantSignedConditionedValue {k ell : ℕ}
    (F : MarkedPhysicalMarking PS k → GiantTwoSidedFullResidue PS →
      MarkedPhysicalMarking PB (k+ell) → GiantSignedMemory PB → ℂ)
    (i : GiantSignedConditionedIndex PS (PB := PB) k ell) : ℂ :=
  F i.1 i.2.2.1 i.2.2.2 i.2.1

def giantSignedConditionedEnergy {k ell : ℕ} (ν : ∀ g, PB g → ℝ)
    (F : MarkedPhysicalMarking PS k → GiantTwoSidedFullResidue PS →
      MarkedPhysicalMarking PB (k+ell) → GiantSignedMemory PB → ℂ) : ℝ≥0∞ :=
  ∑' i : GiantSignedConditionedIndex PS (PB := PB) k ell,
    ENNReal.ofReal (giantSignedConditionedWeight PS ν i * ‖giantSignedConditionedValue PS F i‖ ^ 2)

def giantSignedConditionedPairing {k ell : ℕ} (ν : ∀ g, PB g → ℝ)
    (F G : MarkedPhysicalMarking PS k → GiantTwoSidedFullResidue PS →
      MarkedPhysicalMarking PB (k+ell) → GiantSignedMemory PB → ℂ) : ℂ :=
  ∑' i : GiantSignedConditionedIndex PS (PB := PB) k ell,
    (giantSignedConditionedWeight PS ν i : ℂ) *
      star (giantSignedConditionedValue PS F i) * giantSignedConditionedValue PS G i

omit [DecidableEq S] [DecidableEq B]
  [∀ p : ↥(markedPhysicalBandPrimes PS), NeZero p.val] in
theorem giantSignedConditionedWeight_nonneg {k ell : ℕ}
    (ν : ∀ g, PB g → ℝ) (hν : ∀ g p, 0 ≤ ν g p)
    (i : GiantSignedConditionedIndex PS (PB := PB) k ell) :
    0 ≤ giantSignedConditionedWeight PS ν i :=
  mul_nonneg (mul_nonneg (giantSignedSmallHaar_nonneg PS)
    (giantSignedMemoryMass_nonneg ν hν i.2.1))
    (Finset.prod_nonneg fun g _ => Finset.prod_nonneg fun j _ => hν g (i.2.2.2 g j))

theorem giantSignedConditionedEnergy_eq {k ell : ℕ} (ν : ∀ g, PB g → ℝ)
    (F : MarkedPhysicalMarking PS k → GiantTwoSidedFullResidue PS →
      MarkedPhysicalMarking PB (k+ell) → GiantSignedMemory PB → ℂ) :
    giantSignedConditionedEnergy PS ν F =
      ∑ d : MarkedPhysicalMarking PS k, giantSignedAmbientEnergy PS ν (F d) := by
  simp only [giantSignedConditionedEnergy, GiantSignedConditionedIndex,
    ENNReal.tsum_prod', tsum_fintype, Fintype.sum_prod_type, giantSignedConditionedWeight,
    giantSignedConditionedValue, giantSignedAmbientEnergy]

omit [DecidableEq S] [DecidableEq B]
  [∀ p : ↥(markedPhysicalBandPrimes PS), NeZero p.val] in
theorem giantSignedConditionedPairing_summable {k ell : ℕ}
    (ν : ∀ g, PB g → ℝ) (hν : ∀ g p, 0 ≤ ν g p)
    (F G : MarkedPhysicalMarking PS k → GiantTwoSidedFullResidue PS →
      MarkedPhysicalMarking PB (k+ell) → GiantSignedMemory PB → ℂ)
    (hF : giantSignedConditionedEnergy PS ν F ≠ ∞)
    (hG : giantSignedConditionedEnergy PS ν G ≠ ∞) :
    Summable (fun i : GiantSignedConditionedIndex PS (PB := PB) k ell =>
      (giantSignedConditionedWeight PS ν i : ℂ) *
        star (giantSignedConditionedValue PS F i) * giantSignedConditionedValue PS G i) :=
  giantSignedWeightedPairing_summable_of_energy (giantSignedConditionedWeight PS ν)
    (giantSignedConditionedWeight_nonneg PS ν hν) _ _ hF hG

omit [DecidableEq S] [DecidableEq B]
  [∀ p : ↥(markedPhysicalBandPrimes PS), NeZero p.val] in
theorem giantSignedConditionedPairing_energy {k ell : ℕ}
    (ν : ∀ g, PB g → ℝ) (hν : ∀ g p, 0 ≤ ν g p)
    (F G : MarkedPhysicalMarking PS k → GiantTwoSidedFullResidue PS →
      MarkedPhysicalMarking PB (k+ell) → GiantSignedMemory PB → ℂ)
    (hF : giantSignedConditionedEnergy PS ν F ≠ ∞)
    (hG : giantSignedConditionedEnergy PS ν G ≠ ∞) :
    ENNReal.ofReal (‖giantSignedConditionedPairing PS ν F G‖ ^ 2) ≤
      giantSignedConditionedEnergy PS ν F * giantSignedConditionedEnergy PS ν G :=
  giantSignedWeightedPairing_energy (giantSignedConditionedWeight PS ν)
    (giantSignedConditionedWeight_nonneg PS ν hν) _ _ hF hG

end
end ArtinMatthews
