module

public import ArtinMatthews.MarkedMajorLabelPolynomial
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Data.Nat.Factorial.DoubleFactorial
public import Mathlib.NumberTheory.Chebyshev
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


set_option backward.privateInPublic true
@[expose] public section

/-! Exact first-band separation for the actual injective prime-label
product set. The unshared remaining label product is retained literally. -/
namespace ArtinMatthews
open Finset

 theorem markedMajorLabelSet_sum {J : Type*} [Fintype J] [DecidableEq J] (P : J → Finset ℕ)
    (hP : ∀ j p, p ∈ P j → p.Prime)
    (hdis : Pairwise (fun i j => Disjoint (P i) (P j))) (f : ℕ → ℂ) :
    (∑ b ∈ markedMajorLabelSet P,f b) = ∑ t : (j : J) → ↥(P j),f (markedPrimeBandProduct P t) := by
  classical
  rw [markedMajorLabelSet,sum_image (fun _ _ _ _ h => markedPrimeBandProduct_injective P hP hdis h)]
  congr 1
  ext t
  simp

 theorem markedMajorLabelSet_option_sum {J : Type*} [Fintype J] [DecidableEq J] (P₀ : Finset ℕ) (P : J → Finset ℕ)
    (hP₀ : ∀ p ∈ P₀,p.Prime) (hP : ∀ j p,p ∈ P j → p.Prime)
    (hdis₀ : ∀ j,Disjoint P₀ (P j)) (hdis : Pairwise (fun i j => Disjoint (P i) (P j)))
    (f : ℕ → ℂ) :
    (∑ b ∈ markedMajorLabelSet (fun j : Option J => j.elim P₀ P),f b) =
      ∑ p ∈ P₀,∑ b ∈ markedMajorLabelSet P,f (p*b) := by
  classical
  let Q := fun j : Option J => j.elim P₀ P
  have hQ : ∀ j p,p ∈ Q j → p.Prime := by
    intro j p hp
    cases j with
    | none => exact hP₀ p hp
    | some j => exact hP j p hp
  have hdQ : Pairwise (fun i j => Disjoint (Q i) (Q j)) := by
    intro i j hij
    cases i with
    | none =>
      cases j with
      | none => exact (hij rfl).elim
      | some j => exact hdis₀ j
    | some i =>
      cases j with
      | none => exact (hdis₀ i).symm
      | some j => exact hdis (fun h => hij (congrArg Option.some h))
  rw [markedMajorLabelSet_sum Q hQ hdQ]
  have he := (Equiv.piOptionEquivProd (β := fun j : Option J => ↥(Q j))).symm.sum_comp
    (fun t => f (markedPrimeBandProduct Q t))
  calc
    _ = ∑ v : ↥P₀ × ((j : J) → ↥(P j)),f (v.1.val*markedPrimeBandProduct P v.2) := by
      convert he.symm using 1
      simp only [markedPrimeBandProduct,Fintype.prod_option,
        Equiv.piOptionEquivProd_symm_apply]
      congr 1
    _ = ∑ p : ↥P₀,∑ t : (j : J) → ↥(P j),f (p.val*markedPrimeBandProduct P t) :=
      Fintype.sum_prod_type _
    _ = ∑ p : ↥P₀,∑ b ∈ markedMajorLabelSet P,f (p.val*b) := by
      apply sum_congr rfl
      intro p _
      exact (markedMajorLabelSet_sum P hP hdis (fun b => f (p.val*b))).symm
    _ = _ := sum_coe_sort P₀ (fun p => ∑ b ∈ markedMajorLabelSet P,f (p*b))

 theorem markedMajorLabelMass_option {J : Type*} [Fintype J] [DecidableEq J] (P₀ : Finset ℕ) (P : J → Finset ℕ) :
    markedMajorLabelMass (fun j : Option J => j.elim P₀ P) =
      (bandReciprocalMass P₀)⁻¹*markedMajorLabelMass P := by
  simp only [markedMajorLabelMass,Fintype.prod_option,Option.elim_none,Option.elim_some]

end ArtinMatthews
