module

public import ArtinMatthews.GiantCandidateResidueCRT
public import ArtinMatthews.RoughCharacterDensity
public import ArtinMatthews.GiantCandidateResidueTruncation
public import ArtinMatthews.RoughBonferroniLayerBounds
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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

/-! Finite rough residue counts with their actual Euler product and
the quantitative sieve remainder before the scale is chosen. -/

namespace ArtinMatthews
noncomputable section
open Finset
open scoped BigOperators

theorem giantCandidateRoughResidueIoc_error_le (P : Finset ℕ) (r M N Q a : ℕ)
    (hMN : M ≤ N) (hQ : 0 < Q) (hP : ∀ p∈P,p.Prime) (hcop : ∀ p∈P,p.Coprime Q) :
    let H := ((N-M:ℕ):ℝ)/(Q:ℝ)
    |((giantCandidateRoughResidueIoc P M N Q a).card:ℝ)-H*roughCharacterEulerDensity P| ≤
      2*H*(∑ S ∈ P.powersetCard (r+1),1/(roughSubsetDivisor S:ℝ)) +
      ((P.powersetCard (r+1)).card:ℝ)+((roughTruncationSubsets P r).card:ℝ) := by
  let H := ((N-M:ℕ):ℝ)/(Q:ℝ)
  let E := ∑ S ∈ P.powersetCard (r+1),1/(roughSubsetDivisor S:ℝ)
  let C := ((giantCandidateRoughResidueIoc P M N Q a).card:ℂ)
  let T := giantCandidateRoughResidueTruncation P r M N Q a
  let A := ((H*roughCharacterDensityTruncation P r:ℝ):ℂ)
  let B := ((H*roughCharacterEulerDensity P:ℝ):ℂ)
  have hH : 0 ≤ H := by dsimp [H]; positivity
  have htr : ‖C-T‖ ≤ H*E+((P.powersetCard (r+1)).card:ℝ) :=
    giantCandidateRoughResidueTruncation_error_le P r M N Q a hMN hQ hP hcop
  have hmain : ‖T-A‖ ≤ ((roughTruncationSubsets P r).card:ℝ) :=
    giantCandidateRoughResidueTruncation_main_error_le P r M N Q a hMN hQ hP hcop
  have hdens : ‖A-B‖ ≤ H*E := by
    dsimp only [A,B]
    rw [← Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs,← mul_sub,abs_mul,abs_of_nonneg hH]
    exact mul_le_mul_of_nonneg_left (roughCharacterDensityTruncation_error_le P r hP) hH
  change |((giantCandidateRoughResidueIoc P M N Q a).card:ℝ)-H*roughCharacterEulerDensity P| ≤ _
  rw [← Real.norm_eq_abs,← Complex.norm_real,Complex.ofReal_sub,Complex.ofReal_natCast]
  change ‖C-B‖ ≤ 2*H*E+((P.powersetCard (r+1)).card:ℝ)+((roughTruncationSubsets P r).card:ℝ)
  have h₁ : ‖C-B‖ ≤ ‖C-T‖+‖T-B‖ := by
    simpa only [dist_eq_norm] using dist_triangle C T B
  have h₂ : ‖T-B‖ ≤ ‖T-A‖+‖A-B‖ := by
    simpa only [dist_eq_norm] using dist_triangle T A B
  linarith only [h₁,h₂,htr,hmain,hdens]

theorem giantCandidateRoughResidueIoc_error_numeric (P : Finset ℕ) (r M N Q a v : ℕ)
    (hMN : M ≤ N) (hQ : 0 < Q) (hP : ∀ p∈P,p.Prime)
    (hcop : ∀ p∈P,p.Coprime Q) (hheight : ∀ p∈P,p≤v) (hv : 1≤v) :
    let H := ((N-M:ℕ):ℝ)/(Q:ℝ)
    |((giantCandidateRoughResidueIoc P M N Q a).card:ℝ)-H*roughCharacterEulerDensity P| ≤
      2*H*((∑ p∈P,1/(p:ℝ))^(r+1)/((r+1).factorial:ℝ)) +
      (v:ℝ)^(r+1)+((r+1:ℕ):ℝ)*(v:ℝ)^r := by
  let H := ((N-M:ℕ):ℝ)/(Q:ℝ)
  have hH : 0 ≤ H := by dsimp [H]; positivity
  have hcard₁ : ((P.powersetCard (r+1)).card:ℝ) ≤ (v:ℝ)^(r+1) := by
    exact_mod_cast rough_layer_card_le_pow P (r+1) v hP hheight
  have hcard₂ : ((roughTruncationSubsets P r).card:ℝ) ≤ ((r+1:ℕ):ℝ)*(v:ℝ)^r := by
    exact_mod_cast roughTruncationSubsets_card_le_pow P r v hP hheight hv
  exact (giantCandidateRoughResidueIoc_error_le P r M N Q a hMN hQ hP hcop).trans
    (add_le_add (add_le_add
      (mul_le_mul_of_nonneg_left (rough_layer_reciprocal_mass_le_factorial P (r+1))
        (mul_nonneg (by norm_num) hH)) hcard₁) hcard₂)

end
end ArtinMatthews
