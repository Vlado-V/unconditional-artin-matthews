module

public import ArtinMatthews.IdealPhaseFactor
public import ArtinMatthews.IdealFiniteFrame
public import ArtinMatthews.IdealGroupedAtom
public import ArtinMatthews.MarkedMinorArcGram
public import ArtinMatthews.IdealGroupedBilinear
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
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.WittVector.IsPoly
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
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! The original Mellin factor is a unit-modulus twist of each arbitrary
ordered-label test in the genuine integer bilinear estimate. -/
namespace ArtinMatthews
open Finset
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

def idealMellinPhase (ζ : ℝ) (n : ℕ) : ℂ :=
  idealLogPhase ζ 0 (Real.log n)

theorem idealMellinPhase_norm (ζ : ℝ) (n : ℕ) :
    ‖idealMellinPhase ζ n‖ = 1 := idealLogPhase_norm _ _ _

theorem idealProductPhase_eq_mellin (ζ α : ℝ) {n m : ℕ}
    (hn : 0 < n) (hm : 0 < m) :
    idealProductPhase ζ α n m = idealMellinPhase ζ n * idealMellinPhase ζ m *
      (Real.fourierChar (α*(n : ℝ)*(m : ℝ)) : ℂ) := by
  rw [← idealLogPhase_product ζ α hn hm]
  unfold idealMellinPhase idealLogPhase
  rw [Real.exp_add, Real.exp_log (by exact_mod_cast hn),
    Real.exp_log (by exact_mod_cast hm)]
  simp only [mul_zero, zero_mul, add_zero, Real.fourierChar_apply]
  rw [← Complex.exp_add, ← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem idealMellinPhase_energy {Ω : Type*} [Fintype Ω]
    (μ : Ω → ℝ) (p : Ω → ℕ) (f : Ω → ℂ) (ζ : ℝ) :
    idealFrameEnergy μ (fun x => f x * idealMellinPhase ζ (p x)) =
      idealFrameEnergy μ f := by
  simp only [idealFrameEnergy, norm_mul, idealMellinPhase_norm, mul_one]

variable {A B : Type*} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

omit [DecidableEq A] in
theorem idealGroupedProduct_pos (P : A → Finset ℕ) (k : A → ℕ)
    (hP : ∀ i p, p ∈ P i → p.Prime) (x : IdealGroupedLabels P k) :
    0 < idealGroupedProduct x :=
  prod_pos fun i _ => idealGroupProduct_pos hP x i

theorem idealGroupedPhaseBilinear_sq_le
    (P : A → Finset ℕ) (k : A → ℕ) (R : B → Finset ℕ) (l : B → ℕ)
    (hP : ∀ i p, p ∈ P i → p.Prime) (hR : ∀ i p, p ∈ R i → p.Prime)
    (hdisP : Pairwise (fun i j => Disjoint (P i) (P j)))
    (hdisR : Pairwise (fun i j => Disjoint (R i) (R j)))
    (hVP : ∀ i, 0 < bandReciprocalMass (P i)) (hVR : ∀ i, 0 < bandReciprocalMass (R i))
    (L T M N : ℕ) (hL : 0 < L) (hT : 0 < T)
    (f : IdealGroupedLabels P k → ℂ) (g : IdealGroupedLabels R l → ℂ)
    (hf : ∀ x, idealGroupedProduct x ∉ Ico L (L+M) → f x = 0)
    (hg : ∀ y, idealGroupedProduct y ∉ Ico T (T+N) → g y = 0)
    (ζ α : ℝ) (u : ℤ) (q : ℕ) (hq : 0 < q) (hcop : IsCoprime u (q : ℤ))
    (happrox : |α - (u : ℝ)/q| ≤ 1/(q : ℝ)^2) :
    ‖∑ x : IdealGroupedLabels P k, (idealGroupedMass P k x : ℂ) * f x *
      ∑ y : IdealGroupedLabels R l, (idealGroupedMass R l y : ℂ) * g y *
        idealProductPhase ζ α (idealGroupedProduct x) (idealGroupedProduct y)‖^2 ≤
      markedMinorGramBudget M N q *
        ((idealGroupedAtomBudget P k/(L : ℝ)) * idealFrameEnergy (idealGroupedMass P k) f) *
        ((idealGroupedAtomBudget R l/(T : ℝ)) * idealFrameEnergy (idealGroupedMass R l) g) := by
  have hb := idealGroupedBilinear_sq_le P k R l hP hR hdisP hdisR hVP hVR
    L T M N hL hT
    (fun x => f x * idealMellinPhase ζ (idealGroupedProduct x))
    (fun y => g y * idealMellinPhase ζ (idealGroupedProduct y))
    (fun x hx => by rw [hf x hx, zero_mul]) (fun y hy => by rw [hg y hy, zero_mul])
    α u q hq hcop happrox
  rw [idealMellinPhase_energy, idealMellinPhase_energy] at hb
  convert hb using 1
  congr 2
  apply sum_congr rfl
  intro x _
  rw [mul_sum, mul_sum]
  apply sum_congr rfl
  intro y _
  rw [idealProductPhase_eq_mellin ζ α (idealGroupedProduct_pos P k hP x)
    (idealGroupedProduct_pos R l hR y)]
  ring

end
end ArtinMatthews
