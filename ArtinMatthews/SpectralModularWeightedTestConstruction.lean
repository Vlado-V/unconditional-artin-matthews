module

public import ArtinMatthews.SpectralModularWeakTests
public import ArtinMatthews.SpectralGamma0Core
public import ArtinMatthews.SpectralModularDensitySeeds
public import ArtinMatthews.SpectralModularWeightedTestSeeds
public import ArtinMatthews.SpectralSmoothSeedPlaneExtension
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
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
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

/-! Every actual smooth compact interior datum is exactly a pulled-back
weighted plane test.  The height factor is removed by actual smooth division,
and compact support provides the positive height threshold. -/

noncomputable section
open Set
open scoped MatrixGroups ContDiff CompactlySupported

namespace ArtinMatthews

theorem exists_modular_weighted_plane_test (r : SL(2, ℤ))
    (ψ : h2SmoothCompactSeeds) (hψ : tsupport ψ.val ⊆ ModularGroup.fdo) :
    ∃ (Y : ℝ), 0 < Y ∧ ∃ φ : ℝ × ℝ → ℂ,
      ContDiff ℝ ∞ φ ∧ HasCompactSupport φ ∧
      tsupport φ ⊆ {p : ℝ × ℝ | Y < p.2} ∧
      (∀ p ∈ tsupport φ,
        r • UpperHalfPlane.ofComplex (Complex.equivRealProdCLM.symm p) ∈ ModularGroup.fdo) ∧
      ∀ z : UpperHalfPlane, modularPlaneTest r (spectralWeakGradientTest φ) z = ψ.val z := by
  let χ := h2DivideHeightSmoothSeed (modularTranslateSmoothSeed r ψ)
  obtain ⟨Y, hY, φ, hφ, hc, hs, hh, he⟩ :=
    exists_smooth_plane_extension_of_compact_seed χ
  have hχ : tsupport χ.val ⊆
      (fun z : UpperHalfPlane => r • z) ⁻¹' ModularGroup.fdo :=
    (h2DivideHeightSmoothSeed_support _).trans (modularTranslateSmoothSeed_support r ψ hψ)
  refine ⟨Y, hY, φ, hφ, hc, hh, ?_, ?_⟩
  · intro p hp
    obtain ⟨z, hz, rfl⟩ := hs hp
    have hcoords : Complex.equivRealProdCLM.symm (z.re, z.im) = (z : ℂ) :=
      Complex.equivRealProdCLM.symm_apply_apply (z : ℂ)
    rw [hcoords, UpperHalfPlane.ofComplex_apply]
    exact hχ hz
  · intro z
    change (r⁻¹ • z).im • φ ((r⁻¹ • z).re, (r⁻¹ • z).im) = ψ.val z
    rw [he]
    change (r⁻¹ • z).im •
      (h2DivideHeightSmoothSeed (modularTranslateSmoothSeed r ψ)).val (r⁻¹ • z) = ψ.val z
    rw [h2DivideHeightSmoothSeed_apply, modularTranslateSmoothSeed_apply, smul_inv_smul]
    have hn : ((r⁻¹ • z).im : ℂ) ≠ 0 := by exact_mod_cast (r⁻¹ • z).im_ne_zero
    change ((r⁻¹ • z).im : ℂ) * (ψ.val z / ((r⁻¹ • z).im : ℂ)) = ψ.val z
    field_simp

end ArtinMatthews
