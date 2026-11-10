module

public import ArtinMatthews.CubicSieveRoughCorollary
public import ArtinMatthews.CubicSieveExtractionActual
public import ArtinMatthews.CubicSieveMarkedPrimeBound
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

/-! The actual marked prime bound with its cubic Mellin extraction input
discharged. The separate source sampling and divisor-weighted bounds remain
the two analytic inputs of the upper-sieve argument. -/
namespace ArtinMatthews
open Filter OAI OAI.SevenEighths
open scoped ContDiff
noncomputable section

theorem cubicSieve_actual_marked_prime_bound_with_extraction
    {J : Type} [Fintype J] [DecidableEq J]
    (e : J → ℝ) (hinj : Function.Injective e)
    (he : ∀ j,(1/10:ℝ)<e j ∧ e j<(1/5:ℝ))
    (A : ℤ) (hA : A ≠ 0)
    (hnoncube : ¬ ∃ y : OAI.CubicFirstMoment.Eisenstein,y^3=(A:OAI.CubicFirstMoment.Eisenstein))
    {M : ℕ} [NeZero M] (χ : DirichletCharacter ℂ M)
    {ε : ℝ} (hε : 0 < ε) (hεq : ε < 1/4)
    (Φ : ℝ → ℝ) (hΦ : ContDiff ℝ ∞ Φ) (hΦ₀ : ∀ t,0 ≤ Φ t) (hΦ₁ : ∀ t,‖Φ t‖ ≤ 1)
    (hs : Function.support Φ ⊆ Set.Ioo 1 2)
    (hdepth : 100*(5*(30:ℝ)+36)<(Fintype.card J:ℝ))
    (hsource : ∃ Cν : ℝ, 0 < Cν ∧ ∀ᶠ x : ℝ in atTop,
      GiantSamplingShiftedBilinearBound (cubicNumeratorHeckeCharacter A hA) Φ x (ε/1024) Cν)
    (m : ℕ) (C : ℝ) (herror : CubicSieveDivisorWeightedBound e Φ ε m C)
    (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ x : ℝ in atTop, cubicSieveNormalizedScale e x*
      ‖markedActualPrimeThetaSum e (cubicNumeratorHeckeCharacter A hA) χ
        (giantMarkedCenteredCore ε) Φ 3 x‖ ≤
      C*Real.exp (-(2*(m:ℝ)))/(cubicSieveSourceExponent ε m)^2+δ := by
  have he' (j : J) : 0 < e j ∧ e j ≤ 1/5 :=
    ⟨(by norm_num : (0:ℝ)<1/10).trans (he j).1,(he j).2.le⟩
  have hγ := (cubicSieve_sourceExponent_bounds hε hεq m).1
  have hSupp : Function.support Φ ⊆ Set.Icc 1 3 :=
    hs.trans (fun _ ht => ⟨ht.1.le,ht.2.le.trans (by norm_num)⟩)
  have hb := cubicSieveExtractionBoxSaving_actual e hinj he A hA hnoncube χ Φ hΦ
    hSupp (cubicSieveSourceExponent ε m) hγ hε hεq hdepth
  exact cubicSieve_actual_marked_prime_bound e he' A hA hnoncube χ hε hεq
    Φ hΦ hΦ₀ hΦ₁ hs hsource m C herror hb δ hδ

end
end ArtinMatthews
