module

public import ArtinMatthews.MarkedPhysicalActualLineMain
public import ArtinMatthews.MarkedPhysicalBadRootEstimate
public import ArtinMatthews.MarkedPhysicalBadRootLogBound
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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

/-! The actual residue-and-union-label Haar main term after UV
normalization. No growing residue or label cardinality remains. -/

noncomputable section
namespace ArtinMatthews
open Filter
open scoped BigOperators

theorem markedPhysicalActualUnionLineMain_normalized_bound
    {J : Type*} [Fintype J] [DecidableEq J]
    (e : J → ℝ) (he : ∀ j, (1/10 : ℝ) ≤ e j) (hinj : Function.Injective e) (T : ℝ) :
    ∀ᶠ x : ℝ in atTop,
      ∀ (hdis : Pairwise (fun i j => Disjoint (markedLogPowerBand (e i) x) (markedLogPowerBand (e j) x)))
        (d₀ Y : ℝ), Real.exp ((Real.log x)^(1/10 : ℝ)) ≤ Y →
      ∀ U V A B C D : ℝ, 0 < U → 0 < V →
        U ≤ A → A ≤ B → B ≤ 16*U → V ≤ C → C ≤ D → D ≤ 2*V →
      ∀ (R Q W : ℝ) (ψ : ℝ → ℂ),
        1 ≤ Q → 1 ≤ Y → 0 ≤ R → 0 ≤ W →
        (∀ v, ‖ψ v‖ ≤ W) → (∀ v, ψ v ≠ 0 → |v| ≤ R) →
        markedPhysicalActualUnionLineMain e x hdis d₀ Y A B C D R Q ψ / (U*V) ≤
          (16/(riemannZeta 2).re) * ((33*W*(8*R+5))*Q^3) * (Real.log x)^(-T) := by
  filter_upwards [markedPhysicalActualUnionLineMain_log_saving e he hinj T,
    eventually_gt_atTop (1 : ℝ)] with x hx hx1
  intro hdis d₀ Y hY U V A B C D hU hV hUA hAB hB hVC hCD hD
    R Q W ψ hQ hYone hR hW hψ hsupp
  have hh := hx hdis d₀ Y hY A B C D hAB hCD R Q W ψ hQ hYone hR hW hψ hsupp
  have harea := markedPhysicalRoot_normalized_area_le hU hV hUA hAB hB hVC hCD hD
  have hscale : 0 ≤ (1/(riemannZeta 2).re) * ((33*W*(8*R+5))*Q^3) * (Real.log x)^(-T) := by
    have hz := markedPhysicalRoot_zeta_two_pos
    have hlog := (Real.log_pos hx1).le
    positivity
  calc
    _ ≤ (((B-A)*(D-C)/(riemannZeta 2).re) *
        ((33*W*(8*R+5))*Q^3) * (Real.log x)^(-T))/(U*V) :=
      div_le_div_of_nonneg_right hh (mul_pos hU hV).le
    _ = ((B-A)*(D-C)/(U*V)) *
        ((1/(riemannZeta 2).re) * ((33*W*(8*R+5))*Q^3) * (Real.log x)^(-T)) := by ring
    _ ≤ 16 * ((1/(riemannZeta 2).re) * ((33*W*(8*R+5))*Q^3) * (Real.log x)^(-T)) :=
      mul_le_mul_of_nonneg_right harea hscale
    _ = _ := by ring

theorem markedPhysicalActualUnionLineMain_normalized_log_saving
    {J : Type*} [Fintype J] [DecidableEq J]
    (e : J → ℝ) (he : ∀ j, (1/10 : ℝ) ≤ e j) (hinj : Function.Injective e)
    (A₀ G : ℝ) :
    ∀ᶠ x : ℝ in atTop,
      ∀ (hdis : Pairwise (fun i j => Disjoint (markedLogPowerBand (e i) x) (markedLogPowerBand (e j) x)))
        (d₀ Y : ℝ), Real.exp ((Real.log x)^(1/10 : ℝ)) ≤ Y →
      ∀ U V A B C D : ℝ, 0 < U → 0 < V →
        U ≤ A → A ≤ B → B ≤ 16*U → V ≤ C → C ≤ D → D ≤ 2*V →
      ∀ (R Q W : ℝ) (ψ : ℝ → ℂ),
        1 ≤ Q → Q ≤ (Real.log x)^A₀ → 1 ≤ Y → 0 ≤ R → 0 ≤ W →
        (∀ v, ‖ψ v‖ ≤ W) → (∀ v, ψ v ≠ 0 → |v| ≤ R) →
        markedPhysicalActualUnionLineMain e x hdis d₀ Y A B C D R Q ψ / (U*V) ≤
          (16/(riemannZeta 2).re) * (33*W*(8*R+5)) * (Real.log x)^(-G) := by
  filter_upwards [markedPhysicalActualUnionLineMain_normalized_bound e he hinj (G+3*A₀),
    eventually_gt_atTop (1 : ℝ)] with x hx hx1
  intro hdis d₀ Y hY U V A B C D hU hV hUA hAB hB hVC hCD hD
    R Q W ψ hQ hQlog hYone hR hW hψ hsupp
  have hh := hx hdis d₀ Y hY U V A B C D hU hV hUA hAB hB hVC hCD hD
    R Q W ψ hQ hYone hR hW hψ hsupp
  have hpow := markedPhysicalRoot_log_cube_cancel (G := G) (Real.log_pos hx1)
    (zero_le_one.trans hQ) hQlog
  have hfac : 0 ≤ (16/(riemannZeta 2).re) * (33*W*(8*R+5)) := by
    have hz := markedPhysicalRoot_zeta_two_pos
    positivity
  apply hh.trans
  calc
    _ = ((16/(riemannZeta 2).re) * (33*W*(8*R+5))) *
        (Q^3 * (Real.log x)^(-(G+3*A₀))) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hpow hfac

end ArtinMatthews
