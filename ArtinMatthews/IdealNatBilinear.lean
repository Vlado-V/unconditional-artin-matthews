module

public import ArtinMatthews.MarkedMinorArcGram
public import Mathlib.Analysis.Complex.Circle
public import ArtinMatthews.IdealIntegerBilinear
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
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
public import Mathlib.Order.Interval.Finset.Box
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

/-! The integer Gram estimate on literal positive product intervals. -/
namespace ArtinMatthews
open Finset
open scoped BigOperators
noncomputable section

 theorem idealNatInterval_sum {R : Type*} [AddCommMonoid R]
    (f : ℤ → R) (L M : ℕ) :
    (∑ z ∈ Ico (L : ℤ) ((L : ℤ)+(M : ℤ)), f z) =
      ∑ n ∈ Ico L (L+M), f (n : ℤ) := by
  classical
  symm
  refine sum_bij (fun n _ => (n : ℤ)) ?_ ?_ ?_ ?_
  · intro n hn
    obtain ⟨hlo, hhi⟩ := mem_Ico.mp hn
    exact mem_Ico.mpr ⟨by exact_mod_cast hlo, by exact_mod_cast hhi⟩
  · intro n hn m hm he
    exact_mod_cast he
  · intro z hz
    obtain ⟨hlo, hhi⟩ := mem_Ico.mp hz
    have hz0 : 0 ≤ z := le_trans (Int.natCast_nonneg L) hlo
    have he : (z.toNat : ℤ) = z := Int.toNat_of_nonneg hz0
    refine ⟨z.toNat, mem_Ico.mpr ⟨?_, ?_⟩, he⟩ <;> omega
  · intro n _
    rfl

theorem idealNatBilinear_sq_le (L T M N : ℕ) (α : ℝ) (u : ℤ)
    (q : ℕ) (hq : 0 < q) (hcop : IsCoprime u (q : ℤ))
    (happrox : |α - (u : ℝ)/q| ≤ 1/(q : ℝ)^2) (a b : ℕ → ℂ) :
    ‖∑ h ∈ Ico L (L+M), a h *
      ∑ n ∈ Ico T (T+N), b n * (Real.fourierChar (α*(h : ℝ)*n) : ℂ)‖^2 ≤
      markedMinorGramBudget M N q *
        (∑ h ∈ Ico L (L+M), ‖a h‖^2) *
        (∑ n ∈ Ico T (T+N), ‖b n‖^2) := by
  have hh := idealIntegerBilinear_sq_le (L : ℤ) (T : ℤ) M N α u q hq hcop happrox
    (fun z => a z.toNat) (fun z => b z.toNat)
  simp_rw [idealNatInterval_sum, Int.toNat_natCast, Int.cast_natCast] at hh
  exact hh

end
end ArtinMatthews
