module

public import ArtinMatthews.IdealCellPhaseComparison
public import ArtinMatthews.IdealCellLogVariationActual
public import ArtinMatthews.IdealCellLogVariationUniform
public import ArtinMatthews.IdealRationalCellUniform
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

/-! The actual original complex phase is uniformly approximated on
retained cells for every small-denominator rational approximation. -/
namespace ArtinMatthews
open Filter
open scoped BigOperators Topology
noncomputable section
attribute [local instance] Classical.propDecidable

universe u v

theorem idealMajorCellComparison_uniform (a c d X B₀ C D v₀ : ℝ)
    (ha : 0 ≤ a) (hc : 0 < c) (hd : 0 ≤ d) (hX : 0 ≤ X)
    (hB : 0 ≤ B₀) (hC : 0 ≤ C) (hD : 0 ≤ D) (hv₀ : 0 < v₀) :
    ∀ᶠ L : ℝ in atTop, ∀ (A : Type u) (B : Type v)
      [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B],
      ∀ (Q r : ℕ) [NeZero r], (Q : ℝ) ≤ L^a → r ≤ Q →
        ∀ (P : A → Finset ℕ) (R : B → Finset ℕ),
        (∀ i p, p ∈ P i → p.Prime) → (∀ i p, p ∈ R i → p.Prime) →
        (∀ i, 0 < bandReciprocalMass (P i)) → (∀ i, 0 < bandReciprocalMass (R i)) →
        (∀ i p, p ∈ P i → Real.exp (L^c) ≤ (p : ℝ) ∧ (p : ℝ) ≤ Real.exp (L^d)) →
        (∀ i p, p ∈ R i → Real.exp (L^c) ≤ (p : ℝ) ∧ (p : ℝ) ≤ Real.exp (L^d)) →
        ∀ (i : A) (k : B), IdealPrimeInterval (P i) → IdealPrimeInterval (R k) →
        v₀ ≤ bandReciprocalMass (P i) → v₀ ≤ bandReciprocalMass (R k) →
        ∀ (u : ℤ) (ζ β : ℝ) (x : IdealSelectedLabels P) (y : IdealSelectedLabels R),
          |ζ| ≤ L^C → |β| * (idealSelectedProduct x : ℝ)*(idealSelectedProduct y : ℝ) ≤ L^B₀ →
          L^(-X) ≤ idealLogCellMass P (L^(-idealMajorCellExponent a B₀ C (D+1)))
            (idealLogCell (L^(-idealMajorCellExponent a B₀ C (D+1))) x) →
          L^(-X) ≤ idealLogCellMass R (L^(-idealMajorCellExponent a B₀ C (D+1)))
            (idealLogCell (L^(-idealMajorCellExponent a B₀ C (D+1))) y) →
          ‖idealProductPhase ζ ((u : ℝ)/r+β) (idealSelectedProduct x) (idealSelectedProduct y) -
            idealFullCellPhaseAverage P R Q (L^(-idealMajorCellExponent a B₀ C (D+1)))
              (L^(-X)) ζ ((u : ℝ)/r+β) x y‖ ≤ L^(-D) := by
  filter_upwards [idealRationalCellAverage_uniform.{u,v} a c d X (D+1) v₀
    ha hc hd hX (by positivity) hv₀,
    idealCellLogVariation_uniform.{u,v} a B₀ C (D+1) ha hB hC (by positivity),
    eventually_ge_atTop (2 : ℝ)] with L hrat hvar hL2
  have hL : 0 < L := by linarith
  intro A B _ _ _ _ Q r _ hQ hQr P R hP hR hVP hVR hboundsP hboundsR i k hintervalP hintervalR
    hVloP hVloR u ζ β x y hζ hβ hx hy
  let h := L^(-idealMajorCellExponent a B₀ C (D+1))
  have hh : 0 < h := Real.rpow_pos_of_pos hL _
  have hr := hrat A B Q r hQ hQr P R hP hR hVP hVR hboundsP hboundsR i k
    hintervalP hintervalR hVloP hVloR h hh u x y hx hy
  have hv := hvar A B P R hP hR hVP hVR Q r hQ (L^(-X)) (Real.rpow_pos_of_pos hL _)
    ζ β u x y hζ hβ
  have hs := idealCellPhaseComparison_split P R hP hR Q r h (L^(-X)) ζ β u x y
  refine hs.trans ((add_le_add hr hv).trans ?_)
  calc
    _ = (2/L)*L^(-D) := by
      rw [show -(D+1) = -1 + -D by ring, Real.rpow_add hL, Real.rpow_neg_one]
      ring
    _ ≤ 1*L^(-D) := mul_le_mul_of_nonneg_right ((div_le_one₀ hL).mpr hL2) (Real.rpow_nonneg hL.le _)
    _ = _ := one_mul _

end
end ArtinMatthews
