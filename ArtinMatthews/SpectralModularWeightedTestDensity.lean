module

public import ArtinMatthews.SpectralModularWeakTests
public import ArtinMatthews.SpectralModularDensitySmooth
public import ArtinMatthews.SpectralModularWeightedTestConstruction
public import ArtinMatthews.SpectralModularWeightedTestSeeds
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.CStarAlgebra.Module.Constructions
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

/-! The actual weighted pulled-back plane tests separate the full modular
`L²` space.  No density of weighted tests is postulated: each smooth compact
interior datum is realized by an explicit inverse-height construction. -/

noncomputable section
open Set MeasureTheory
open scoped MatrixGroups ContDiff CompactlySupported

namespace ArtinMatthews

/-- The exact tests in the completed weak-gradient identity have trivial
annihilator in the actual modular `L²` space. -/
theorem modular_weighted_test_annihilator_eq_zero (r : SL(2, ℤ))
    (f : Lp ℂ 2 (volume.restrict ModularGroup.fd))
    (hvanish : ∀ (Y : ℝ), 0 < Y → ∀ φ : ℝ × ℝ → ℂ,
      ContDiff ℝ ∞ φ → HasCompactSupport φ →
      tsupport φ ⊆ {p : ℝ × ℝ | Y < p.2} →
      (∀ p ∈ tsupport φ,
        r • UpperHalfPlane.ofComplex (Complex.equivRealProdCLM.symm p) ∈ ModularGroup.fdo) →
      (∫ z in ModularGroup.fd,
        f z * modularPlaneTest r (spectralWeakGradientTest φ) z) = 0) : f = 0 := by
  have hinner (g : Lp ℂ 2 (volume.restrict ModularGroup.fd))
      (hg : ∃ ψ : h2SmoothCompactSeeds, tsupport ψ.val ⊆ ModularGroup.fdo ∧
        g =ᵐ[volume.restrict ModularGroup.fd] ψ.val) : inner ℂ g f = 0 := by
    obtain ⟨ψ, hψ, hgeq⟩ := hg
    obtain ⟨Y, hY, φ, hφ, hc, hh, hchart, he⟩ :=
      exists_modular_weighted_plane_test r (h2ConjugateSmoothSeed ψ)
        ((h2ConjugateSmoothSeed_support ψ).trans hψ)
    have hz := hvanish Y hY φ hφ hc hh hchart
    rw [L2.inner_def]
    calc
      (∫ z, inner ℂ (g z) (f z) ∂volume.restrict ModularGroup.fd) =
          ∫ z in ModularGroup.fd,
            f z * modularPlaneTest r (spectralWeakGradientTest φ) z := by
        apply integral_congr_ae
        filter_upwards [hgeq] with z hgz
        rw [hgz, he, h2ConjugateSmoothSeed_apply]
        simp only [RCLike.inner_apply']
        exact mul_comm (star (ψ.val z)) (f z)
      _ = 0 := hz
  have hall : ∀ g : Lp ℂ 2 (volume.restrict ModularGroup.fd), inner ℂ g f = 0 :=
    fun g => modular_smooth_compact_supported_dense.induction hinner
      (isClosed_eq (continuous_id.inner continuous_const) continuous_const) g
  exact inner_self_eq_zero.mp (hall f)

end ArtinMatthews
