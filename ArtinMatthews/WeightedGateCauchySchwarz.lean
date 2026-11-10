module

public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Star.Real
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
public import Mathlib.RingTheory.WittVector.IsPoly
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
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! Weighted gate mass controls the first factor in Cauchy–Schwarz.
The vectors may depend on every variable entering the gate. -/
namespace ArtinMatthews
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

theorem weightedGate_norm_sq_le {I : Type*} [Fintype I]
    (w : I → ℝ) (hw : ∀ i, 0 ≤ w i) (gate : I → Prop) (z : I → ℂ)
    (ε : ℝ) (hmass : (∑ i, if gate i then w i else 0) ≤ ε) :
    ‖∑ i, (w i : ℂ) * (if gate i then z i else 0)‖ ^ 2 ≤
      ε * ∑ i, w i * ‖z i‖ ^ 2 := by
  let a : I → ℝ := fun i => if gate i then w i else 0
  have ha (i : I) : 0 ≤ a i := by
    dsimp [a]
    split_ifs
    · exact hw i
    · exact le_rfl
  have hn : ‖∑ i, (w i : ℂ) * (if gate i then z i else 0)‖ ≤
      ∑ i, a i * ‖z i‖ := by
    apply (norm_sum_le _ _).trans_eq
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : gate i
    · have he : a i = w i := ite_eq_left hi
      rw [he, ite_eq_left hi, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (hw i)]
    · have he : a i = 0 := ite_eq_right hi
      rw [he, ite_eq_right hi, mul_zero, norm_zero, zero_mul]
  have hc := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul Finset.univ
    (r := fun i => a i * ‖z i‖) (f := a) (g := fun i => w i * ‖z i‖ ^ 2)
    (fun i _ => ha i) (fun i _ => mul_nonneg (hw i) (sq_nonneg _))
    (by
      intro i _
      by_cases hi : gate i
      · have he : a i = w i := ite_eq_left hi
        rw [he]
        exact le_of_eq (by ring)
      · have he : a i = 0 := ite_eq_right hi
        rw [he]
        simp)
  have hsquare := (sq_le_sq₀ (norm_nonneg _)
    (Finset.sum_nonneg (fun i _ => mul_nonneg (ha i) (norm_nonneg _)))).mpr hn
  exact hsquare.trans (hc.trans (mul_le_mul_of_nonneg_right hmass
    (Finset.sum_nonneg (fun i _ => mul_nonneg (hw i) (sq_nonneg _)))))

end
end ArtinMatthews
