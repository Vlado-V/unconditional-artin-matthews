module

public import ArtinMatthews.SLocalNormOneHaar
public import ArtinMatthews.QuotientPeriodization
public import ArtinMatthews.SLocalNormOneTopology
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
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

/-! The genuine norm-one source quotient has the exact unfolding law
for the diagonal sixth-power periodization, with its induced Haar
normalization and integrability derived. -/
namespace ArtinMatthews.SourcePhysical

open NumberField IsDedekindDomain MeasureTheory
open scoped NumberField Classical
noncomputable section
variable (K : Type) [Field K] [NumberField K]
variable (S : Finset (HeightOneSpectrum (𝓞 K)))

def sNormOnePeriodize (f : SNormOne K S → ℂ) : SNormOneSixthQuotient K S → ℂ :=
  quotientPeriodize (sNormOneSixthSubgroup K S) f

@[simp] theorem sNormOnePeriodize_mk (f : SNormOne K S → ℂ) (x : SNormOne K S) :
    sNormOnePeriodize K S f (sNormOneSixthQuotientMap K S x) =
      ∑' a : (sNormOneSixthSubgroup K S).op, f (a • x) := rfl

theorem sNormOnePeriodize_unfold (ν : Measure (SNormOne K S)) [ν.IsHaarMeasure]
    (f : SNormOne K S → ℂ) (hfm : Measurable f) (hfi : Integrable f ν) :
    Integrable (sNormOnePeriodize K S f) (sNormOneQuotientMeasure K S ν) ∧
      (∫ y, sNormOnePeriodize K S f y ∂sNormOneQuotientMeasure K S ν) = ∫ x, f x ∂ν := by
  let : Countable (sNormOneSixthSubgroup K S) := sNormOneSixthSubgroup_countable K S
  exact quotientPeriodize_unfold (sNormOneSixthSubgroup K S) ν
    (sNormOneFundamentalDomain K S ν) f hfm hfi

end
end ArtinMatthews.SourcePhysical
