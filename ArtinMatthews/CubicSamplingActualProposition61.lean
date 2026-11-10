module

public import ArtinMatthews.CubicSamplingCentered
public import ArtinMatthews.GiantSamplingShiftedInput
public import ArtinMatthews.CubicSamplingProposition61Linear
public import ArtinMatthews.ShiftedABLActualBilinearSource
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
public import Mathlib.Order.CompletePartialOrder
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

/-! The constructed source estimate supplies the original power loss
in Proposition 6.1 for every fixed linear combination of marking arrays. -/

noncomputable section
namespace ArtinMatthews

open Filter Set OAI
open scoped BigOperators ContDiff

theorem cubicNumerator_shiftedBilinearBound_eventually
    (A : ℤ) (hA : A ≠ 0)
    (hnoncube : ¬ ∃ y : OAI.CubicFirstMoment.Eisenstein,
      y^3=(A : OAI.CubicFirstMoment.Eisenstein))
    (Φ : ℝ → ℝ) (hΦ : ContDiff ℝ ∞ Φ)
    (hs : Function.support Φ ⊆ Icc (1 : ℝ) 2)
    {ν : ℝ} (hν : 0 < ν) :
    ∃ Cν : ℝ, 0 < Cν ∧ ∀ᶠ x : ℝ in atTop,
      GiantSamplingShiftedBilinearBound (cubicNumeratorHeckeCharacter A hA) Φ x ν Cν := by
  obtain ⟨Cν,hCν,hbound⟩ := cubicNumerator_shiftedBilinearBound A hA hnoncube Φ hΦ hs ν hν
  refine ⟨Cν,hCν,?_⟩
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
  exact hbound x hx

theorem giantCubicSampling_proposition61_actual
    {I : Type*} [Fintype I] {J : I → Type*} [∀ i, Fintype (J i)]
    (e : ∀ i, J i → ℝ) (he : ∀ i j, 0 < e i j ∧ e i j ≤ 1/5) (c : I → ℂ)
    (A : ℤ) (hA : A ≠ 0)
    (hnoncube : ¬ ∃ y : OAI.CubicFirstMoment.Eisenstein,
      y^3=(A : OAI.CubicFirstMoment.Eisenstein))
    {M : ℕ} [NeZero M] (χ : DirichletCharacter ℂ M)
    {ε : ℝ} (hε : 0 < ε) (hεq : ε < 1/4)
    (Φ : ℝ → ℝ) (hΦ : ContDiff ℝ ∞ Φ) (hΦ₁ : ∀ t, ‖Φ t‖ ≤ 1)
    (hs : Function.support Φ ⊆ Ioo (1 : ℝ) 2) (G : ℝ) :
    ∀ᶠ x : ℝ in atTop,
      (∑ r ∈ Finset.Icc 1 ⌊x^(ε/64)⌋₊,
        ‖giantCubicSamplingCenteredSum (cubicNumeratorHeckeCharacter A hA) χ
          (fun u => ∑ i, c i*(literalMarkedArrayWeight (e i) x u : ℂ)) Φ ε x r‖) ≤
        x*(Real.log x)^(-G) :=
  giantCubicSampling_proposition61 e he c A hA hnoncube χ hε hεq Φ hΦ hΦ₁ hs
    (cubicNumerator_shiftedBilinearBound_eventually A hA hnoncube Φ hΦ
      (hs.trans Ioo_subset_Icc_self) (div_pos hε (by norm_num))) G

end ArtinMatthews
