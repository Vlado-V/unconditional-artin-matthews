module

public import ArtinMatthews.IdealKernelTranspose
public import ArtinMatthews.IdealCharacterCellSupport
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
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

/-! Moving the actual character-cell kernel onto an arbitrary dyadic
test enlarges its product interval by an absolute factor only. -/
namespace ArtinMatthews
open Finset
noncomputable section
attribute [local instance] Classical.propDecidable

variable {I : Type*} [Fintype I] [DecidableEq I]

theorem idealCharacterCellTranspose_product_support (P : I → Finset ℕ)
    (hP : ∀ i p, p ∈ P i → p.Prime) (Q : ℕ) {h ξ U V : ℝ}
    (hh : 0 < h) (hU : 0 < U) (hV : 0 < V) (f : IdealSelectedLabels P → ℂ)
    (hf : ∀ z, f z ≠ 0 → U ≤ (idealSelectedProduct z : ℝ) ∧
      (idealSelectedProduct z : ℝ) ≤ V) (x : IdealSelectedLabels P)
    (hx : idealCharacterCellTranspose P Q h ξ f x ≠ 0) :
    U*Real.exp (-h) < (idealSelectedProduct x : ℝ) ∧
      (idealSelectedProduct x : ℝ) < V*Real.exp h := by
  have hstar : idealCharacterCellApply P Q h ξ (fun z => star (f z)) x ≠ 0 := by
    intro he
    apply hx
    rw [idealCharacterCellTranspose_eq, he, star_zero]
  exact idealCharacterCellApply_product_support P hP Q hh hU hV (fun z => star (f z))
    (fun z hz => hf z (fun he => hz (by rw [he, star_zero]))) x hstar

theorem idealCharacterCellTranspose_dyadic_support (P : I → Finset ℕ)
    (hP : ∀ i p, p ∈ P i → p.Prime) (Q : ℕ) {h ξ : ℝ} (hh : 0 < h)
    (hexp : Real.exp h ≤ 2) (U : ℕ) (hU : 0 < U) (f : IdealSelectedLabels P → ℂ)
    (hf : ∀ z, idealSelectedProduct z ∉ Ico (2*U) (4*U) → f z = 0) :
    ∀ x, idealSelectedProduct x ∉ Ico U (U+8*U) →
      idealCharacterCellTranspose P Q h ξ f x = 0 := by
  intro x hx
  by_contra hn
  have hUr : (0 : ℝ) < U := by exact_mod_cast hU
  have hs := idealCharacterCellTranspose_product_support P hP Q hh
    (show 0 < 2*(U : ℝ) by positivity) (show 0 < 4*(U : ℝ) by positivity) f
    (fun z hz => by
      have hm : idealSelectedProduct z ∈ Ico (2*U) (4*U) := by
        by_contra hm
        exact hz (hf z hm)
      exact ⟨by exact_mod_cast (mem_Ico.mp hm).1,
        by exact_mod_cast (mem_Ico.mp hm).2.le⟩) x hn
  have hlo : 1/2 ≤ Real.exp (-h) := by
    rw [Real.exp_neg]
    simpa only [one_div] using one_div_le_one_div_of_le (Real.exp_pos h) hexp
  have hnl : (U : ℝ) < (idealSelectedProduct x : ℝ) := by
    have hm := mul_le_mul_of_nonneg_left hlo (show 0 ≤ 2*(U : ℝ) by positivity)
    nlinarith [hs.1]
  have hnr : (idealSelectedProduct x : ℝ) < (U : ℝ)+8*(U : ℝ) := by
    have hm := mul_le_mul_of_nonneg_left hexp (show 0 ≤ 4*(U : ℝ) by positivity)
    nlinarith [hs.2]
  apply hx
  exact mem_Ico.mpr ⟨by exact_mod_cast hnl.le, by exact_mod_cast hnr⟩

end
end ArtinMatthews
