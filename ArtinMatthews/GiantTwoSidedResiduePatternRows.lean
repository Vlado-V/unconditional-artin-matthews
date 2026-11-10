module

public import ArtinMatthews.GiantTwoSidedResiduePatternKernel
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

/-! Absolute row and column estimates for the full residue-state kernel. -/
namespace ArtinMatthews
open Finset
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

def giantTwoSidedResiduePatternAbsoluteRow {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset ℕ} [∀ p : ↥(markedPhysicalBandPrimes P),NeZero p.val]
    {k ell : ℕ} {C : J → Finset (Fin k)} (step : ℤ) (q ζ : ℝ)
    (K : GiantTwoSidedPatternCoefficient P C ell) (s : GiantTwoSidedResidueState P (k+ell)) : ℝ :=
  ∑ a : GiantTwoSidedPatternAuxiliary P C,∑ t : GiantTwoSidedResidueState P (k+ell),
    ‖giantTwoSidedResiduePatternCoefficient step q ζ K s t a‖

def giantTwoSidedResiduePatternAbsoluteColumn {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset ℕ} [∀ p : ↥(markedPhysicalBandPrimes P),NeZero p.val]
    {k ell : ℕ} {C : J → Finset (Fin k)} (step : ℤ) (q ζ : ℝ)
    (K : GiantTwoSidedPatternCoefficient P C ell) (t : GiantTwoSidedResidueState P (k+ell)) : ℝ :=
  ∑ a : GiantTwoSidedPatternAuxiliary P C,∑ s : GiantTwoSidedResidueState P (k+ell),
    ‖giantTwoSidedResiduePatternCoefficient step q ζ K s t a‖

theorem giantTwoSidedResiduePatternAbsoluteColumn_eq_reverse {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset ℕ} [∀ p : ↥(markedPhysicalBandPrimes P),NeZero p.val]
    (hP : ∀ j p,p∈P j → p.Prime) (hV : ∀ j,0<bandReciprocalMass (P j))
    {k ell : ℕ} {C : J → Finset (Fin k)} (step : ℤ) {q : ℝ} (hq : 0≤q) (ζ : ℝ)
    (K : GiantTwoSidedPatternCoefficient P C ell) (t : GiantTwoSidedResidueState P (k+ell)) :
    giantTwoSidedResiduePatternAbsoluteColumn step q ζ K t=
      giantTwoSidedResiduePatternAbsoluteRow (-step) q ζ (fun b c a => K c b a) t := by
  unfold giantTwoSidedResiduePatternAbsoluteColumn giantTwoSidedResiduePatternAbsoluteRow
  apply sum_congr rfl
  intro a _
  apply sum_congr rfl
  intro s _
  have hr : GiantTwoSidedResiduePatternCondition C step s t a ↔
      GiantTwoSidedResiduePatternCondition C (-step) t s a := by
    constructor
    · exact giantTwoSidedResiduePatternCondition_reverse C step s t a
    · intro h
      simpa only [neg_neg] using giantTwoSidedResiduePatternCondition_reverse C (-step) t s a h
  rw [giantTwoSidedResiduePatternCoefficient_norm hP hV _ hq,
    giantTwoSidedResiduePatternCoefficient_norm hP hV _ hq,← hr]
  split_ifs
  · ring
  · rfl

theorem giantTwoSidedResiduePatternAbsoluteRow_le {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset ℕ} [∀ p : ↥(markedPhysicalBandPrimes P),NeZero p.val]
    (hP : ∀ j p,p∈P j → p.Prime)
    (hdis : Pairwise (fun i j => Disjoint (P i) (P j))) (hV : ∀ j,0<bandReciprocalMass (P j))
    {k ell : ℕ} {C : J → Finset (Fin k)} (step : ℤ) {q B K₀ : ℝ}
    (hq : 0<q) (hq1 : q≤1) (hB : 0≤B) (hK₀ : 0≤K₀) (ζ : ℝ)
    (K : GiantTwoSidedPatternCoefficient P C ell) (hK : ∀ b c a,‖K b c a‖≤K₀)
    (hbudget : ∀ (j : J) (z : ℕ),
      (bandReciprocalMass (P j))⁻¹^(ell+(C j).card)*
      ((z:ℝ)+((ell+(C j).card:ℕ):ℝ))^(ell+(C j).card)*q^((z:ℝ)/2)≤B)
    (s : GiantTwoSidedResidueState P (k+ell)) :
    giantTwoSidedResiduePatternAbsoluteRow step q ζ K s≤K₀*B^Fintype.card J := by
  let D (r : GiantTwoSidedFullResidue P) := giantTwoSidedResidueDamping P (k+ell) q r
  let W := giantTwoSidedPatternFreshMass P C ell
  let coeff := giantTwoSidedResiduePatternCoefficient step q ζ K s
  have hD (r : GiantTwoSidedFullResidue P) : D r∈Set.Icc (0:ℝ) 1 :=
    giantTwoSidedResidueDamping_mem_unitInterval P (k+ell) ⟨hq.le,hq1⟩ r
  have hW : 0≤W := giantTwoSidedPatternFreshMass_nonneg C ell hV
  have hrow (a : GiantTwoSidedPatternAuxiliary P C) :
      (∑ t : GiantTwoSidedResidueState P (k+ell),‖coeff t a‖)≤
        giantTwoSidedPatternAuxiliaryMass a*(K₀*B^Fintype.card J) := by
    let T := giantTwoSidedResiduePatternTargets step s a
    let μ := giantTwoSidedPatternAuxiliaryMass a
    have hμ : 0≤μ := giantTwoSidedPatternAuxiliaryMass_nonneg hV a
    have hsum : (∑ t∈T,‖coeff t a‖)=∑ t : GiantTwoSidedResidueState P (k+ell),‖coeff t a‖ := by
      apply sum_subset (subset_univ _)
      intro t _ ht
      have hf : ¬GiantTwoSidedResiduePatternCondition C step s t a :=
        fun h => ht (mem_filter.mpr ⟨mem_univ _,h⟩)
      exact (giantTwoSidedResiduePatternCoefficient_norm hP hV step hq.le ζ K s t a).trans (ite_eq_right hf)
    rw [← hsum]
    by_cases hT : T.Nonempty
    · obtain ⟨t₀,ht₀⟩ := hT
      let r := t₀.val.1
      have hcard : (T.card:ℝ)*W*D r≤B^Fintype.card J :=
        giantTwoSidedResiduePatternTargets_budget hP hdis ht₀ hq hV hbudget
      calc
        _ ≤ ∑ _t∈T,μ*K₀*(W*D r) := by
          apply sum_le_sum
          intro t ht
          have hv : GiantTwoSidedResiduePatternCondition C step s t a := (mem_filter.mp ht).2
          have hr : t.val.1=r := giantTwoSidedResiduePatternTargets_position ht ht₀
          have heq : ‖coeff t a‖=μ*W*‖K s.val.2 t.val.2 a‖*D s.val.1*D t.val.1 :=
            (giantTwoSidedResiduePatternCoefficient_norm hP hV step hq.le ζ K s t a).trans (ite_eq_left hv)
          rw [heq,hr]
          have hterm : ‖K s.val.2 t.val.2 a‖*D s.val.1≤K₀ :=
            (mul_le_of_le_one_right (norm_nonneg _) (hD _).2).trans (hK _ _ _)
          calc
            _ = (μ*W)*(‖K s.val.2 t.val.2 a‖*D s.val.1)*D r := by ring
            _ ≤ (μ*W)*K₀*D r := mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hterm (mul_nonneg hμ hW)) (hD _).1
            _ = _ := by ring
        _ = μ*K₀*((T.card:ℝ)*W*D r) := by rw [sum_const,nsmul_eq_mul]; ring
        _ ≤ μ*K₀*B^Fintype.card J := mul_le_mul_of_nonneg_left hcard (mul_nonneg hμ hK₀)
        _ = _ := mul_assoc _ _ _
    · rw [Finset.not_nonempty_iff_eq_empty.mp hT,sum_empty]
      exact mul_nonneg hμ (mul_nonneg hK₀ (pow_nonneg hB _))
  unfold giantTwoSidedResiduePatternAbsoluteRow
  calc
    _ ≤ ∑ a : GiantTwoSidedPatternAuxiliary P C,
        giantTwoSidedPatternAuxiliaryMass a*(K₀*B^Fintype.card J) := sum_le_sum fun a _ => hrow a
    _ = _ := by rw [← sum_mul,giantTwoSidedPatternAuxiliaryMass_sum C hV,one_mul]

def giantTwoSidedResiduePatternAbsoluteEntry {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset ℕ} {k ell : ℕ} {C : J → Finset (Fin k)} (step : ℤ) (q ζ : ℝ)
    (K : GiantTwoSidedPatternCoefficient P C ell) (s t : GiantTwoSidedResidueState P (k+ell)) : ℝ :=
  ∑ a : GiantTwoSidedPatternAuxiliary P C,‖giantTwoSidedResiduePatternCoefficient step q ζ K s t a‖

def giantTwoSidedResiduePatternOperator {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset ℕ} [∀ p : ↥(markedPhysicalBandPrimes P),NeZero p.val]
    {k ell : ℕ} {C : J → Finset (Fin k)} (step : ℤ) (q ζ : ℝ)
    (K : GiantTwoSidedPatternCoefficient P C ell) (f : GiantTwoSidedResidueState P (k+ell) → ℂ)
    (s : GiantTwoSidedResidueState P (k+ell)) : ℂ :=
  ∑ t : GiantTwoSidedResidueState P (k+ell),
    (∑ a : GiantTwoSidedPatternAuxiliary P C,giantTwoSidedResiduePatternCoefficient step q ζ K s t a)*f t

end
end ArtinMatthews
