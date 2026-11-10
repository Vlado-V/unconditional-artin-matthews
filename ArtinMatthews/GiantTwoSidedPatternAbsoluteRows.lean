module

public import ArtinMatthews.GiantTwoSidedPatternKernel
public import ArtinMatthews.GiantTwoSidedPatternTargetBudget
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

/-! The actual absolute transition sums first keep each auxiliary
choice and each permitted target. Taking absolute values before any
averaging preserves the true row and reversed-column normalizations. -/
namespace ArtinMatthews
open Finset
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

def giantTwoSidedPatternAbsoluteRow {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset ℕ} {k ell : ℕ} {C : J → Finset (Fin k)} (step : ℤ) (q ζ : ℝ)
    (K : GiantTwoSidedPatternCoefficient P C ell) {Z : Finset ℕ} (Z' : Finset ℕ)
    (s : GiantTwoSidedEndpointState P (k+ell) Z) : ℝ :=
  ∑ a : GiantTwoSidedPatternAuxiliary P C,∑ t : GiantTwoSidedEndpointState P (k+ell) Z',
    ‖giantTwoSidedPatternPhysicalCoefficient step q ζ K s t a‖

def giantTwoSidedPatternAbsoluteColumn {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset ℕ} {k ell : ℕ} {C : J → Finset (Fin k)} (step : ℤ) (q ζ : ℝ)
    (K : GiantTwoSidedPatternCoefficient P C ell) (Z : Finset ℕ) {Z' : Finset ℕ}
    (t : GiantTwoSidedEndpointState P (k+ell) Z') : ℝ :=
  ∑ a : GiantTwoSidedPatternAuxiliary P C,∑ s : GiantTwoSidedEndpointState P (k+ell) Z,
    ‖giantTwoSidedPatternPhysicalCoefficient step q ζ K s t a‖

theorem giantTwoSidedPatternAbsoluteColumn_eq_reverse {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset ℕ} (hP : ∀ j p,p∈P j → p.Prime) (hV : ∀ j,0 < bandReciprocalMass (P j))
    {k ell : ℕ} {C : J → Finset (Fin k)} (step : ℤ) {q : ℝ} (hq : 0 ≤ q) (ζ : ℝ)
    (K : GiantTwoSidedPatternCoefficient P C ell) (Z : Finset ℕ) {Z' : Finset ℕ}
    (t : GiantTwoSidedEndpointState P (k+ell) Z') :
    giantTwoSidedPatternAbsoluteColumn step q ζ K Z t =
      giantTwoSidedPatternAbsoluteRow (-step) q ζ (fun b c a => K c b a) Z t := by
  unfold giantTwoSidedPatternAbsoluteColumn giantTwoSidedPatternAbsoluteRow
  apply sum_congr rfl
  intro a _
  apply sum_congr rfl
  intro s _
  have hr : GiantTwoSidedPatternCondition C step s t a ↔ GiantTwoSidedPatternCondition C (-step) t s a := by
    constructor
    · exact giantTwoSidedPatternCondition_reverse C step s t a
    · intro h
      simpa only [neg_neg] using giantTwoSidedPatternCondition_reverse C (-step) t s a h
  rw [giantTwoSidedPatternPhysicalCoefficient_norm hP hV _ hq,
    giantTwoSidedPatternPhysicalCoefficient_norm hP hV _ hq,← hr]
  split_ifs
  · ring
  · rfl

theorem giantTwoSidedPatternAbsoluteRow_le {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset ℕ} (hP : ∀ j p,p∈P j → p.Prime)
    (hdis : Pairwise (fun i j => Disjoint (P i) (P j))) (hV : ∀ j,0 < bandReciprocalMass (P j))
    {k ell : ℕ} {C : J → Finset (Fin k)} (step : ℤ) {q B K₀ : ℝ}
    (hq : 0 < q) (hq1 : q ≤ 1) (hB : 0 ≤ B) (hK₀ : 0 ≤ K₀) (ζ : ℝ)
    (K : GiantTwoSidedPatternCoefficient P C ell)
    (hK : ∀ b c a,‖K b c a‖ ≤ K₀)
    (hbudget : ∀ (j : J) (z : ℕ),
      (bandReciprocalMass (P j))⁻¹^(ell+(C j).card)*
      ((z:ℝ)+((ell+(C j).card:ℕ):ℝ))^(ell+(C j).card)*q^((z:ℝ)/2) ≤ B)
    {Z : Finset ℕ} (Z' : Finset ℕ) (s : GiantTwoSidedEndpointState P (k+ell) Z) :
    giantTwoSidedPatternAbsoluteRow step q ζ K Z' s ≤ K₀*B^Fintype.card J := by
  let D (n : ℕ) := giantTwoSidedEndpointDamping P (k+ell) q n
  let W := giantTwoSidedPatternFreshMass P C ell
  let coeff := giantTwoSidedPatternPhysicalCoefficient step q ζ K s (Z':=Z')
  have hD (n : ℕ) : D n ∈ Set.Icc (0:ℝ) 1 :=
    giantTwoSidedEndpointDamping_mem_unitInterval P (k+ell) ⟨hq.le,hq1⟩ n
  have hW : 0 ≤ W := giantTwoSidedPatternFreshMass_nonneg C ell hV
  have hrow (a : GiantTwoSidedPatternAuxiliary P C) :
      (∑ t : GiantTwoSidedEndpointState P (k+ell) Z',‖coeff t a‖) ≤
        giantTwoSidedPatternAuxiliaryMass a*(K₀*B^Fintype.card J) := by
    let T := giantTwoSidedPatternTargets step Z' s a
    let μ := giantTwoSidedPatternAuxiliaryMass a
    have hμ : 0 ≤ μ := giantTwoSidedPatternAuxiliaryMass_nonneg hV a
    have hsum : (∑ t ∈ T,‖coeff t a‖) = ∑ t : GiantTwoSidedEndpointState P (k+ell) Z',‖coeff t a‖ := by
      apply sum_subset (subset_univ _)
      intro t _ ht
      have hf : ¬GiantTwoSidedPatternCondition C step s t a := fun h => ht (mem_filter.mpr ⟨mem_univ _,h⟩)
      exact (giantTwoSidedPatternPhysicalCoefficient_norm hP hV step hq.le ζ K s t a).trans (ite_eq_right hf)
    rw [← hsum]
    by_cases hT : T.Nonempty
    · obtain ⟨t₀,ht₀⟩ := hT
      let n := t₀.val.1.val
      have hcard : (T.card:ℝ)*W*D n ≤ B^Fintype.card J :=
        giantTwoSidedPatternTargets_budget hdis ht₀ hq hV hbudget
      calc
        _ ≤ ∑ _t ∈ T,μ*K₀*(W*D n) := by
          apply sum_le_sum
          intro t ht
          have hv : GiantTwoSidedPatternCondition C step s t a := (mem_filter.mp ht).2
          have hn : t.val.1.val=n := congrArg (fun v : ↥Z' => v.val)
            (giantTwoSidedPatternTargets_position ht ht₀)
          have heq : ‖coeff t a‖ = μ*W*‖K s.val.2 t.val.2 a‖*D s.val.1.val*D t.val.1.val :=
            (giantTwoSidedPatternPhysicalCoefficient_norm hP hV step hq.le ζ K s t a).trans (ite_eq_left hv)
          rw [heq,hn]
          have hterm : ‖K s.val.2 t.val.2 a‖*D s.val.1.val ≤ K₀ :=
            (mul_le_of_le_one_right (norm_nonneg _) (hD _).2).trans (hK _ _ _)
          calc
            _ = (μ*W)*(‖K s.val.2 t.val.2 a‖*D s.val.1.val)*D n := by ring
            _ ≤ (μ*W)*K₀*D n := mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hterm (mul_nonneg hμ hW)) (hD _).1
            _ = _ := by ring
        _ = μ*K₀*((T.card:ℝ)*W*D n) := by rw [sum_const,nsmul_eq_mul]; ring
        _ ≤ μ*K₀*B^Fintype.card J := mul_le_mul_of_nonneg_left hcard (mul_nonneg hμ hK₀)
        _ = _ := mul_assoc _ _ _
    · rw [Finset.not_nonempty_iff_eq_empty.mp hT,sum_empty]
      exact mul_nonneg hμ (mul_nonneg hK₀ (pow_nonneg hB _))
  unfold giantTwoSidedPatternAbsoluteRow
  calc
    _ ≤ ∑ a : GiantTwoSidedPatternAuxiliary P C,
        giantTwoSidedPatternAuxiliaryMass a*(K₀*B^Fintype.card J) := sum_le_sum fun a _ => hrow a
    _ = _ := by rw [← sum_mul,giantTwoSidedPatternAuxiliaryMass_sum C hV,one_mul]

end
end ArtinMatthews
