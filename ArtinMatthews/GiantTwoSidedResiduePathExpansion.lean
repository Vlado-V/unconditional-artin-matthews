module

public import ArtinMatthews.GiantTwoSidedResiduePathMass
public import ArtinMatthews.GiantTwoSidedResidueRootSum
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

/-! Expanding each edge sums the actual pattern, two slot permutations
and auxiliary assignment. The normalized full expansion is exact. -/
namespace ArtinMatthews
open Finset
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

abbrev GiantTwoSidedResidueEdgeChoice {I J : Type*} {P : J → Finset ℕ} {k : ℕ}
    (patterns : Finset I) (C : I → J → Finset (Fin k)) (ell : ℕ) :=
  Σ ν : ↥patterns,(J → Equiv.Perm (Fin (k+ell))) ×
    (J → Equiv.Perm (Fin (k+ell))) × GiantTwoSidedPatternAuxiliary P (C ν.val)

def giantTwoSidedResidueSlotNormalization {J : Type*} [Fintype J] [DecidableEq J] (M : ℕ) : ℝ :=
  ((Fintype.card (J → Equiv.Perm (Fin M)):ℝ)^2)⁻¹

def giantTwoSidedResidueChoiceCoefficient {I J : Type*} [Fintype J]
    {P : J → Finset ℕ} {k ell : ℕ} {patterns : Finset I} {C : I → J → Finset (Fin k)}
    (step : ℤ) (q ζ : ℝ) (K : ∀ ν,GiantTwoSidedPatternCoefficient P (C ν) ell)
    (choice : GiantTwoSidedResidueEdgeChoice (P:=P) patterns C ell)
    (s t : GiantTwoSidedResidueState P (k+ell)) : ℝ :=
  ‖giantTwoSidedResiduePatternCoefficient step q ζ (K choice.1.val)
    (giantTwoSidedResiduePermute choice.2.1 s)
    (giantTwoSidedResiduePermute choice.2.2.1 t) choice.2.2.2‖

theorem giantTwoSidedResidueFamilyAbsoluteEntry_expand {I J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset ℕ} {k ell : ℕ} (patterns : Finset I) (C : I → J → Finset (Fin k))
    (step : ℤ) (q ζ : ℝ) (K : ∀ ν,GiantTwoSidedPatternCoefficient P (C ν) ell)
    (s t : GiantTwoSidedResidueState P (k+ell)) :
    giantTwoSidedResidueFamilyAbsoluteEntry patterns C step q ζ K s t=
      ∑ choice : GiantTwoSidedResidueEdgeChoice (P:=P) patterns C ell,
        giantTwoSidedResidueSlotNormalization (J:=J) (k+ell)*
          giantTwoSidedResidueChoiceCoefficient step q ζ K choice s t := by
  let Permutations := J → Equiv.Perm (Fin (k+ell))
  have hs : (∑ choice : GiantTwoSidedResidueEdgeChoice (P:=P) patterns C ell,
      giantTwoSidedResidueChoiceCoefficient step q ζ K choice s t)=
      ∑ ν∈patterns,∑ π : Permutations,∑ τ : Permutations,
        ∑ a : GiantTwoSidedPatternAuxiliary P (C ν),
          ‖giantTwoSidedResiduePatternCoefficient step q ζ (K ν)
            (giantTwoSidedResiduePermute π s) (giantTwoSidedResiduePermute τ t) a‖ := by
    rw [Fintype.sum_sigma,← sum_coe_sort patterns]
    apply sum_congr rfl
    intro ν _
    simp only [Fintype.sum_prod_type,giantTwoSidedResidueChoiceCoefficient]
    rfl
  rw [← mul_sum,hs]
  unfold giantTwoSidedResidueFamilyAbsoluteEntry giantTwoSidedResidueSlotAverage
    giantTwoSidedResiduePatternAbsoluteEntry giantTwoSidedResidueSlotNormalization
  rw [← sum_div]
  rw [div_eq_mul_inv,mul_comm]

def giantTwoSidedResidueExpandedPathMass {I J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset ℕ} [∀ p : ↥(markedPhysicalBandPrimes P),NeZero p.val]
    {k ell n : ℕ} (patterns : Fin n → Finset I) (C : Fin n → I → J → Finset (Fin k))
    (step : Fin n → ℤ) (q : ℝ) (ζ : Fin n → ℝ)
    (K : ∀ i ν,GiantTwoSidedPatternCoefficient P (C i ν) ell) : ℝ :=
  (giantTwoSidedResidueSlotNormalization (J:=J) (k+ell))^n*
    ∑ choices : (i : Fin n) → GiantTwoSidedResidueEdgeChoice (P:=P) (patterns i) (C i) ell,
      giantTwoSidedResidueFixedPathMass (fun i => C i (choices i).1.val)
        (fun i => (choices i).2.1) (fun i => (choices i).2.2.1)
        (fun i => (choices i).2.2.2) step q ζ (fun i => K i (choices i).1.val)

theorem giantTwoSidedResidueFamilyPathMass_expand {I J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset ℕ} [∀ p : ↥(markedPhysicalBandPrimes P),NeZero p.val]
    {k ell n : ℕ} (patterns : Fin n → Finset I) (C : Fin n → I → J → Finset (Fin k))
    (step : Fin n → ℤ) (q : ℝ) (ζ : Fin n → ℝ)
    (K : ∀ i ν,GiantTwoSidedPatternCoefficient P (C i ν) ell) :
    giantTwoSidedResidueFamilyPathMass patterns C step q ζ K=
      giantTwoSidedResidueExpandedPathMass patterns C step q ζ K := by
  unfold giantTwoSidedResidueFamilyPathMass finiteAbsolutePathMass
  simp_rw [giantTwoSidedResidueFamilyAbsoluteEntry_expand]
  have he (s : Fin (n+1) → GiantTwoSidedResidueState P (k+ell)) :
      (∏ i : Fin n,∑ choice : GiantTwoSidedResidueEdgeChoice (P:=P) (patterns i) (C i) ell,
        giantTwoSidedResidueSlotNormalization (J:=J) (k+ell)*
          giantTwoSidedResidueChoiceCoefficient (step i) q (ζ i) (K i) choice (s i.castSucc) (s i.succ))=
      ∑ choices : (i : Fin n) → GiantTwoSidedResidueEdgeChoice (P:=P) (patterns i) (C i) ell,
        (giantTwoSidedResidueSlotNormalization (J:=J) (k+ell))^n*
          ∏ i : Fin n,giantTwoSidedResidueChoiceCoefficient (step i) q (ζ i) (K i)
            (choices i) (s i.castSucc) (s i.succ) := by
    rw [Fintype.prod_sum]
    apply sum_congr rfl
    intro choices _
    rw [prod_mul_distrib]
    simp
  simp_rw [he,mul_sum]
  rw [sum_comm]
  unfold giantTwoSidedResidueExpandedPathMass giantTwoSidedResidueFixedPathMass
  rw [mul_sum]
  apply sum_congr rfl
  intro choices _
  rw [mul_sum]
  apply sum_congr rfl
  intro s _
  dsimp only [giantTwoSidedResidueChoiceCoefficient]
  ring

def giantTwoSidedResidueExpandedRootMass {I J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset ℕ} [∀ p : ↥(markedPhysicalBandPrimes P),NeZero p.val]
    {k ell n : ℕ} (patterns : Fin n → Finset I) (C : Fin n → I → J → Finset (Fin k))
    (step : Fin n → ℤ) (q : ℝ) (ζ : Fin n → ℝ)
    (K : ∀ i ν,GiantTwoSidedPatternCoefficient P (C i ν) ell) : ℝ :=
  (giantTwoSidedResidueSlotNormalization (J:=J) (k+ell))^n*
    ∑ choices : (i : Fin n) → GiantTwoSidedResidueEdgeChoice (P:=P) (patterns i) (C i) ell,
      giantTwoSidedIndependentFixedPathMass (fun i => C i (choices i).1.val)
        (fun i => (choices i).2.1) (fun i => (choices i).2.2.1)
        (fun i => (choices i).2.2.2) step q ζ (fun i => K i (choices i).1.val)

theorem giantTwoSidedResidueExpandedRootMass_eq {I J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset ℕ} [∀ p : ↥(markedPhysicalBandPrimes P),NeZero p.val]
    (hP : ∀ j p,p∈P j → p.Prime)
    (hdis : Pairwise (fun i j => Disjoint (P i) (P j))) (hV : ∀ j,0<bandReciprocalMass (P j))
    {k ell n : ℕ} (patterns : Fin (n+1) → Finset I)
    (C : Fin (n+1) → I → J → Finset (Fin k)) (step : Fin (n+1) → ℤ)
    {q : ℝ} (hq : 0 ≤ q) (ζ : Fin (n+1) → ℝ)
    (K : ∀ i ν,GiantTwoSidedPatternCoefficient P (C i ν) ell) :
    giantTwoSidedResidueExpandedRootMass patterns C step q ζ K=
      giantTwoSidedResidueFamilyPathMass patterns C step q ζ K := by
  rw [giantTwoSidedResidueFamilyPathMass_expand]
  unfold giantTwoSidedResidueExpandedRootMass giantTwoSidedResidueExpandedPathMass
  congr 1
  apply sum_congr rfl
  intro choices _
  exact (giantTwoSidedResidueFixedPathMass_eq_rootMean hP hdis hV
    (fun i => C i (choices i).1.val)
    (fun i => (choices i).2.1) (fun i => (choices i).2.2.1)
    (fun i => (choices i).2.2.2) step hq ζ (fun i => K i (choices i).1.val)).symm

end
end ArtinMatthews
