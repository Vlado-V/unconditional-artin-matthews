module

public import ArtinMatthews.MarkedTypeIICommonQuotientReindex
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Data.Nat.Factorial.DoubleFactorial
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
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

/-! The common-quotient collision on the original dyadic Cauchy square.
Each noncoprime pair pays one shared-prime density factor. -/

namespace ArtinMatthews
noncomputable section
open Finset
open scoped BigOperators ComplexConjugate

theorem markedTypeII_dyad_collision_norm_le {J : Type*} [Fintype J]
    (P : J → Finset ℕ) (hP : ∀ j p, p ∈ P j → p.Prime)
    (M N H : Finset ℕ) (X : ℕ) (hMN : ∀ v ∈ M×ˢN, v.1*v.2 ≤ X)
    (η : ℝ → ℂ) {Y : ℝ} (hY : 0 < Y) (hη : ∀ u, ‖η u‖ ≤ 1)
    (hsupp : Function.support η ⊆ Set.Icc 1 4)
    (hlabel : ∀ a ∈ markedTypeIIDyadLabels P Y, a^4 ≤ X)
    (α β : ℕ → ℂ) {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hα : ∀ m ∈ M, ‖α m‖ ≤ A) (hβ : ∀ n ∈ N, ‖β n‖ ≤ B) :
    ‖markedTypeIICollisionSum (giantMarkedEndpoints P M N) H
      (markedTypeIIDyadCoefficient P η Y α β)‖ ≤
      128*(markedMajorLabelMass P)^2*(A*B)^2*Y*(X:ℝ)*(1+Real.log (X:ℝ))^3*
        ∑ p ∈ Finset.univ.biUnion P, 1/(p:ℝ)^2 := by
  let L := (markedTypeIIDyadLabels P Y×ˢmarkedTypeIIDyadLabels P Y).filter
    (fun z => ¬ z.1.Coprime z.2)
  let V := markedMajorLabelMass P
  let C := (A*B)^2*(8*(X:ℝ)/Y*(1+Real.log (X:ℝ))^3)
  have hV : 0 ≤ V := prod_nonneg (fun _ _ => inv_nonneg.mpr
    (sum_nonneg (fun _ _ => by positivity)))
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  have hweight (a : ℕ) : ‖(V:ℂ)*η ((a:ℝ)/Y)‖ ≤ V := by
    rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hV]
    exact mul_le_of_le_one_right hV (hη _)
  rw [markedTypeII_dyad_collision_reindex P M N H η hY hsupp α β]
  calc
    _ ≤ ∑ z ∈ L, V^2*C := by
      apply (norm_sum_le _ _).trans
      apply sum_le_sum
      intro z hz
      obtain ⟨ha,hb⟩ := mem_product.mp (mem_filter.mp hz).1
      have hsum : ‖∑ h ∈ H, markedTypeIIQuotientCoefficient M N α β z.1 h *
          conj (markedTypeIIQuotientCoefficient M N α β z.2 h)‖ ≤ C := by
        simpa only [Complex.star_def] using markedTypeII_common_quotient_pair_norm_le M N H α β
          hA hB hY hα hβ (mem_filter.mp ha).2.1 (mem_filter.mp hb).2.1
          (hlabel _ ha) (hlabel _ hb) hMN
      rw [norm_mul,norm_mul,Complex.norm_conj,pow_two]
      exact mul_le_mul (mul_le_mul (hweight _) (hweight _) (norm_nonneg _) hV) hsum
        (norm_nonneg _) (mul_nonneg hV hV)
    _ = (L.card:ℝ)*(V^2*C) := by simp only [sum_const,nsmul_eq_mul]
    _ ≤ ((4*Y)^2 * ∑ p ∈ Finset.univ.biUnion P, 1/(p:ℝ)^2)*(V^2*C) :=
      mul_le_mul_of_nonneg_right (markedTypeIISharedDyadLabels_card_le P hP Y hY)
        (mul_nonneg (sq_nonneg _) hC)
    _ = _ := by
      dsimp only [V,C]
      field_simp [hY.ne']
      ring

end
end ArtinMatthews
