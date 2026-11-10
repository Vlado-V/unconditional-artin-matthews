module

public import ArtinMatthews.IdealFiniteFrame
public import ArtinMatthews.IdealGroupedAtom
public import ArtinMatthews.MarkedMinorArcGram
public import Mathlib.Analysis.Complex.Circle
public import ArtinMatthews.IdealGroupedCollapse
public import ArtinMatthews.IdealNatBilinear
public import ArtinMatthews.IdealNumericReindex
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Star.Real
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

/-! The actual harmonic tuple pairing obeys the integer Gram budget after
its proved numeric-product collapse. No product-only test assumption is used. -/
namespace ArtinMatthews
open Finset
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

variable {A B : Type*} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

theorem idealGroupedBilinear_sq_le
    (P : A → Finset ℕ) (k : A → ℕ) (R : B → Finset ℕ) (l : B → ℕ)
    (hP : ∀ i p, p ∈ P i → p.Prime) (hR : ∀ i p, p ∈ R i → p.Prime)
    (hdisP : Pairwise (fun i j => Disjoint (P i) (P j)))
    (hdisR : Pairwise (fun i j => Disjoint (R i) (R j)))
    (hVP : ∀ i, 0 < bandReciprocalMass (P i)) (hVR : ∀ i, 0 < bandReciprocalMass (R i))
    (L T M N : ℕ) (hL : 0 < L) (hT : 0 < T)
    (f : IdealGroupedLabels P k → ℂ) (g : IdealGroupedLabels R l → ℂ)
    (hf : ∀ x, idealGroupedProduct x ∉ Ico L (L+M) → f x = 0)
    (hg : ∀ y, idealGroupedProduct y ∉ Ico T (T+N) → g y = 0)
    (α : ℝ) (u : ℤ) (q : ℕ) (hq : 0 < q) (hcop : IsCoprime u (q : ℤ))
    (happrox : |α - (u : ℝ)/q| ≤ 1/(q : ℝ)^2) :
    ‖∑ x : IdealGroupedLabels P k, (idealGroupedMass P k x : ℂ) * f x *
      ∑ y : IdealGroupedLabels R l, (idealGroupedMass R l y : ℂ) * g y *
        (Real.fourierChar (α*(idealGroupedProduct x : ℝ)*(idealGroupedProduct y : ℝ)) : ℂ)‖^2 ≤
      markedMinorGramBudget M N q *
        ((idealGroupedAtomBudget P k/(L : ℝ)) * idealFrameEnergy (idealGroupedMass P k) f) *
        ((idealGroupedAtomBudget R l/(T : ℝ)) * idealFrameEnergy (idealGroupedMass R l) g) := by
  let a := idealFiberCoefficient (idealGroupedMass P k) idealGroupedProduct f
  let b := idealFiberCoefficient (idealGroupedMass R l) idealGroupedProduct g
  have he := idealNumeric_bilinear idealGroupedProduct idealGroupedProduct
    (fun x => (idealGroupedMass P k x : ℂ)*f x)
    (fun y => (idealGroupedMass R l y : ℂ)*g y) (Ico L (L+M)) (Ico T (T+N))
    (fun x hx => by rw [hf x hx, mul_zero]) (fun y hy => by rw [hg y hy, mul_zero])
    (fun n m => (Real.fourierChar (α*(n : ℝ)*m) : ℂ))
  rw [he]
  have hbil := idealNatBilinear_sq_le L T M N α u q hq hcop happrox a b
  have hca := idealGroupedCollapse_energy_le P k hP hdisP hVP f (Ico L (L+M))
    (Nat.cast_pos.mpr hL) (fun n hn => by exact_mod_cast (mem_Ico.mp hn).1)
  have hcb := idealGroupedCollapse_energy_le R l hR hdisR hVR g (Ico T (T+N))
    (Nat.cast_pos.mpr hT) (fun n hn => by exact_mod_cast (mem_Ico.mp hn).1)
  change (∑ n ∈ Ico L (L+M), ‖a n‖^2) ≤ _ at hca
  change (∑ n ∈ Ico T (T+N), ‖b n‖^2) ≤ _ at hcb
  change ‖∑ n ∈ Ico L (L+M), a n *
    ∑ m ∈ Ico T (T+N), b m * (Real.fourierChar (α*(n : ℝ)*m) : ℂ)‖^2 ≤ _
  apply hbil.trans
  have hgram := markedMinorGramBudget_nonneg M N q hq
  apply mul_le_mul
  · exact mul_le_mul_of_nonneg_left hca hgram
  · exact hcb
  · exact sum_nonneg fun _ _ => sq_nonneg _
  · exact mul_nonneg hgram ((sum_nonneg fun _ _ => sq_nonneg _).trans hca)

end
end ArtinMatthews
