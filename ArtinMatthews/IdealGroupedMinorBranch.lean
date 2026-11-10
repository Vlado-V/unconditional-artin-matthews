module

public import ArtinMatthews.IdealFiniteFrame
public import ArtinMatthews.IdealGroupedAtom
public import ArtinMatthews.IdealPhaseFactor
public import ArtinMatthews.IdealGroupedPhaseBilinear
public import ArtinMatthews.IdealMinorGramBudget
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

/-! The actual ordered-label minor-arc pairing retains the original
Mellin phase and the derived factorial harmonic atom budget. -/
namespace ArtinMatthews
open Finset
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

variable {A B : Type*} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

omit [DecidableEq A] in
theorem idealGroupedAtomBudget_nonneg (P : A → Finset ℕ) (k : A → ℕ)
    (hV : ∀ i, 0 < bandReciprocalMass (P i)) :
    0 ≤ idealGroupedAtomBudget P k := by
  unfold idealGroupedAtomBudget
  exact prod_nonneg fun i _ => mul_nonneg (Nat.cast_nonneg _)
    (pow_nonneg (inv_nonneg.mpr (hV i).le) _)

theorem idealGroupedPhaseBilinear_minor
    (P : A → Finset ℕ) (k : A → ℕ) (R : B → Finset ℕ) (l : B → ℕ)
    (hP : ∀ i p, p ∈ P i → p.Prime) (hR : ∀ i p, p ∈ R i → p.Prime)
    (hdisP : Pairwise (fun i j => Disjoint (P i) (P j)))
    (hdisR : Pairwise (fun i j => Disjoint (R i) (R j)))
    (hVP : ∀ i, 0 < bandReciprocalMass (P i)) (hVR : ∀ i, 0 < bandReciprocalMass (R i))
    (U V : ℕ) (hU : 0 < U) (hV : 0 < V)
    (f : IdealGroupedLabels P k → ℂ) (g : IdealGroupedLabels R l → ℂ)
    (hf : ∀ x, idealGroupedProduct x ∉ Ico U (U+U) → f x = 0)
    (hg : ∀ y, idealGroupedProduct y ∉ Ico V (V+V) → g y = 0)
    (ζ α : ℝ) (u : ℤ) (r : ℕ) (hr : 0 < r) (hcop : IsCoprime u (r : ℤ))
    (happrox : |α-(u : ℝ)/r| ≤ 1/(r : ℝ)^2)
    {Q S H : ℝ} (hQ : 0 < Q) (hS : 0 < S)
    (hQr : Q ≤ (r : ℝ)) (hrS : (r : ℝ) ≤ (U : ℝ)*(V : ℝ)/S)
    (hH : 1+Real.log (2*(r : ℝ)) ≤ H) :
    ‖∑ x : IdealGroupedLabels P k, (idealGroupedMass P k x : ℂ) * f x *
      ∑ y : IdealGroupedLabels R l, (idealGroupedMass R l y : ℂ) * g y *
        idealProductPhase ζ α (idealGroupedProduct x) (idealGroupedProduct y)‖^2 ≤
      24*(1/(V : ℝ)+1/Q+H/(U : ℝ)+H/S)*
        idealGroupedAtomBudget P k*idealGroupedAtomBudget R l*
        idealFrameEnergy (idealGroupedMass P k) f*
        idealFrameEnergy (idealGroupedMass R l) g := by
  have hb := idealGroupedPhaseBilinear_sq_le P k R l hP hR hdisP hdisR hVP hVR
    U V U V hU hV f g hf hg ζ α u r hr hcop happrox
  have hgram := idealMinorGramBudget_branch U V r hU hV hr hQ hS hQr hrS hH
  have hbp := idealGroupedAtomBudget_nonneg P k hVP
  have hbr := idealGroupedAtomBudget_nonneg R l hVR
  have hef := idealFrameEnergy_nonneg _ (idealGroupedMass_nonneg P k hVP) f
  have heg := idealFrameEnergy_nonneg _ (idealGroupedMass_nonneg R l hVR) g
  refine hb.trans ?_
  calc
    _ = (markedMinorGramBudget U V r/((U : ℝ)*(V : ℝ)))*
        idealGroupedAtomBudget P k*idealGroupedAtomBudget R l*
        idealFrameEnergy (idealGroupedMass P k) f*
        idealFrameEnergy (idealGroupedMass R l) g := by
      simp only [div_eq_mul_inv, mul_inv_rev]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hgram hbp) hbr) hef) heg

end
end ArtinMatthews
