module

public import ArtinMatthews.SpectralModularPartitionGamma0
public import ArtinMatthews.SpectralPeterssonRegionUnfolding
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
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

/-! Real-valued periodization keeps the actual central covering factor. -/
noncomputable section
open Set MeasureTheory

namespace ArtinMatthews

theorem gamma0PeterssonRegion_real_integral_unfold (N : ℕ) (F : UpperHalfPlane → ℝ)
    (hF : Integrable F) :
    (∫ z in gamma0InteriorRegion N, ∑' γ : CongruenceSubgroup.Gamma0 N, F (γ.val⁻¹ • z)) =
      2*(∫ z, F z) := by
  have h := gamma0PeterssonRegion_integral_unfold N (fun z => (F z : ℂ)) hF.ofReal
  have he (z : UpperHalfPlane) :
      (∑' γ : CongruenceSubgroup.Gamma0 N, (F (γ.val⁻¹ • z) : ℂ)) =
        ((∑' γ : CongruenceSubgroup.Gamma0 N, F (γ.val⁻¹ • z) : ℝ) : ℂ) :=
    (Complex.ofReal_tsum _).symm
  simp_rw [he] at h
  rw [integral_complex_ofReal,integral_complex_ofReal] at h
  exact Complex.ofReal_injective (by simpa only [Complex.ofReal_mul,Complex.ofReal_ofNat] using h)

end ArtinMatthews
