module

public import ArtinMatthews.SpectralCuspTwoCellHyperbolic
public import ArtinMatthews.SpectralGamma0EllipticTests
public import ArtinMatthews.SpectralGamma0WeakInverse
public import ArtinMatthews.SpectralSectionLaplacianSeed
public import ArtinMatthews.SpectralCuspCompletedUnfolding
public import ArtinMatthews.SpectralGamma0GlobalWeakLaplacian
public import ArtinMatthews.SpectralSectionLaplacianPullback
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
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
public import Mathlib.RingTheory.SimpleRing.Principal
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
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! The actual ambient Green eigen-equation on every compact cusp test. -/

noncomputable section
open Set MeasureTheory
open scoped MatrixGroups ContDiff InnerProductSpace

namespace ArtinMatthews

theorem gamma0AmbientEigen_compact_weak_laplacian
    (N : ℕ) [NeZero N] (v : gamma0EnergySpace N) (eig : ℝ) (hl : 0 ≤ eig)
    (hG : gamma0Green N (gamma0EnergyInclusion N v) =
      (((eig + 1)⁻¹ : ℝ) : ℂ) • gamma0EnergyInclusion N v) (ψ : h2SmoothCompactSeeds) :
    inner ℂ (gamma0SmoothSeedMass N (h2SectionLaplacianSeed ψ))
      (gamma0EnergyInclusion N v) =
      (eig : ℂ) *
        inner ℂ (gamma0SmoothSeedMass N ψ) (gamma0EnergyInclusion N v) := by
  let a : ℂ := ((eig + 1 : ℝ) : ℂ)
  have ha : a ≠ 0 := Complex.ofReal_ne_zero.mpr (by linarith)
  have hgreen : gamma0Green N (gamma0EnergyInclusion N v) =
      a⁻¹ • gamma0EnergyInclusion N v := by
    simpa only [a, Complex.ofReal_inv] using hG
  have he := gamma0Green_global_weak_laplacian N ψ (gamma0EnergyInclusion N v)
  rw [hgreen, inner_smul_right, inner_add_left] at he
  have hc := congrArg (fun z : ℂ => a * z) he
  simp only [← mul_assoc, mul_inv_cancel₀ ha, one_mul] at hc
  dsimp only [a] at hc
  push_cast at hc
  linear_combination hc

theorem gamma0AmbientEigen_twoCell_weak_laplacian
    (N : ℕ) [NeZero N] (v : gamma0EnergySpace N) (eig : ℝ) (hl : 0 ≤ eig)
    (hG : gamma0Green N (gamma0EnergyInclusion N v) =
      (((eig + 1)⁻¹ : ℝ) : ℂ) • gamma0EnergyInclusion N v)
    (r : SL(2, ℤ)) (Y : ℝ) (hY : 0 < Y) (ψ : h2SmoothCompactSeeds)
    (hs : tsupport ψ.val ⊆ hyperbolicCuspStrip (2*(N : ℝ)) Y) :
    (∫ z in hyperbolicCuspStrip (2*(N : ℝ)) Y,
      inner ℂ (h2SectionPositiveLaplacian ψ.val z)
        (gamma0CuspTwoCellMassRestriction N r Y hY (gamma0EnergyInclusion N v) z)) =
      (eig : ℂ) *
        (∫ z in hyperbolicCuspStrip (2*(N : ℝ)) Y,
          inner ℂ (ψ.val z)
            (gamma0CuspTwoCellMassRestriction N r Y hY (gamma0EnergyInclusion N v) z)) := by
  have hψ : Function.support (fun z => ψ.val z) ⊆ hyperbolicCuspStrip (2*(N : ℝ)) Y :=
    (subset_tsupport _).trans hs
  have hΔψ : Function.support (fun z => (h2SectionLaplacianSeed ψ).val z) ⊆
      hyperbolicCuspStrip (2*(N : ℝ)) Y :=
    (subset_tsupport _).trans ((h2SectionPositiveLaplacian_tsupport_subset ψ).trans hs)
  have he := gamma0AmbientEigen_compact_weak_laplacian N v eig hl hG
    (modularTranslateSmoothSeed r ψ)
  rw [h2SectionLaplacianSeed_modular_pullback,
    gamma0Mass_inner_unfold_twoCell_integral N r Y hY (h2SectionLaplacianSeed ψ) hΔψ _,
    gamma0Mass_inner_unfold_twoCell_integral N r Y hY ψ hψ _] at he
  apply mul_left_cancel₀ (by norm_num : (2 : ℂ) ≠ 0)
  calc
    _ = (eig : ℂ) *
        (2*(∫ z in hyperbolicCuspStrip (2*(N : ℝ)) Y,
          inner ℂ (ψ.val z)
            (gamma0CuspTwoCellMassRestriction N r Y hY (gamma0EnergyInclusion N v) z))) := he
    _ = _ := by ring

theorem gamma0AmbientEigen_native_weak_laplacian
    (N : ℕ) [NeZero N] (v : gamma0EnergySpace N) (eig : ℝ) (hl : 0 ≤ eig)
    (hG : gamma0Green N (gamma0EnergyInclusion N v) =
      (((eig + 1)⁻¹ : ℝ) : ℂ) • gamma0EnergyInclusion N v)
    (r : SL(2, ℤ)) (Y : ℝ) (hY : 0 < Y) (χ : (Fin 2 → ℝ) → ℝ)
    (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ)
    (hs : tsupport χ ⊆ {x : Fin 2 → ℝ | x 0 ∈ Ioc 0 (2*(N : ℝ)) ∧ Y < x 1}) :
    (∫ z in hyperbolicCuspStrip (2*(N : ℝ)) Y,
      inner ℂ (z.im^2*spectralEllipticPositiveLaplacian χ
        (spectralEllipticCoordinates.symm (z.re,z.im)) : ℂ)
        (gamma0CuspTwoCellMassRestriction N r Y hY (gamma0EnergyInclusion N v) z)) =
      (eig : ℂ) *
        (∫ z in hyperbolicCuspStrip (2*(N : ℝ)) Y,
          inner ℂ (χ (spectralEllipticCoordinates.symm (z.re,z.im)) : ℂ)
            (gamma0CuspTwoCellMassRestriction N r Y hY (gamma0EnergyInclusion N v) z)) := by
  have hh : tsupport χ ⊆ {x : Fin 2 → ℝ | 0 < x 1} :=
    fun x hx => hY.trans (hs hx).2
  let ψ := spectralEllipticTestSeed χ hχ hcχ hh
  have hψ : tsupport ψ.val ⊆ hyperbolicCuspStrip (2*(N : ℝ)) Y := by
    intro z hz
    exact hs (spectralEllipticTestSeed_support χ hχ hcχ hh hz)
  simpa only [ψ,spectralEllipticTestSeed_apply,spectralEllipticTestSeed_laplacian] using
    gamma0AmbientEigen_twoCell_weak_laplacian N v eig hl hG r Y hY ψ hψ

end ArtinMatthews
