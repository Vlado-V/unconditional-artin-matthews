module

public import ArtinMatthews.SpectralGamma0CuspVerticalSeed
public import ArtinMatthews.SpectralGamma0EnergyDense
public import ArtinMatthews.SpectralCompactDenseCore
public import ArtinMatthews.SpectralPoincareLinear
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
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! Actual all-positive-height vertical derivative restrictions on the
completed energy domain.  These maps are built from genuine cusp derivatives
and their proved L² energy bounds. -/

noncomputable section
open Set MeasureTheory Filter
open scoped MatrixGroups ContDiff

namespace ArtinMatthews

theorem gamma0CuspVerticalField_add (N : ℕ) [NeZero N] (ψ ξ : h2SmoothCompactSeeds)
    (r : SL(2, ℤ)) (z : UpperHalfPlane) :
    gamma0CuspVerticalField N (ψ + ξ) r z =
      gamma0CuspVerticalField N ψ r z + gamma0CuspVerticalField N ξ r z := by
  have he : gamma0CuspSection N (ψ + ξ) r = gamma0CuspSection N ψ r + gamma0CuspSection N ξ r := by
    funext w
    change arithmeticPoincareSeed _ (ψ.val + ξ.val) (r⁻¹ • w) = _
    rw [arithmeticPoincareSeed_add]
    rfl
  simp only [gamma0CuspVerticalField, he,
    h2SectionGradient_add _ _ (gamma0CuspSection_smooth N ψ r) (gamma0CuspSection_smooth N ξ r)]
  rfl

theorem gamma0CuspVerticalField_smul (N : ℕ) [NeZero N] (c : ℂ) (ψ : h2SmoothCompactSeeds)
    (r : SL(2, ℤ)) (z : UpperHalfPlane) :
    gamma0CuspVerticalField N (c • ψ) r z = c • gamma0CuspVerticalField N ψ r z := by
  have he : gamma0CuspSection N (c • ψ) r = c • gamma0CuspSection N ψ r := by
    funext w
    change arithmeticPoincareSeed _ (c • ψ.val) (r⁻¹ • w) = _
    rw [arithmeticPoincareSeed_smul]
    rfl
  simp only [gamma0CuspVerticalField, he,
    h2SectionGradient_smul c _ (gamma0CuspSection_smooth N ψ r)]
  rfl

def gamma0CuspVerticalSeedLinear (N : ℕ) [NeZero N]
    (r : SL(2, ℤ)) (Y : ℝ) (hY : 0 < Y) :
    h2SmoothCompactSeeds →ₗ[ℂ] CuspHyperbolicL2 (N : ℝ) Y where
  toFun ψ := gamma0CuspVerticalSeedLp N ψ r Y hY
  map_add' ψ ξ := by
    apply Lp.ext
    filter_upwards [gamma0CuspVerticalSeedLp_ae N (ψ + ξ) r Y hY,
      gamma0CuspVerticalSeedLp_ae N ψ r Y hY, gamma0CuspVerticalSeedLp_ae N ξ r Y hY,
      Lp.coeFn_add (gamma0CuspVerticalSeedLp N ψ r Y hY) (gamma0CuspVerticalSeedLp N ξ r Y hY)]
      with z hs hψ hξ hadd
    rw [hadd, hs]
    change _ = (gamma0CuspVerticalSeedLp N ψ r Y hY) z + (gamma0CuspVerticalSeedLp N ξ r Y hY) z
    rw [hψ, hξ, gamma0CuspVerticalField_add]
  map_smul' c ψ := by
    apply Lp.ext
    filter_upwards [gamma0CuspVerticalSeedLp_ae N (c • ψ) r Y hY,
      gamma0CuspVerticalSeedLp_ae N ψ r Y hY,
      Lp.coeFn_smul c (gamma0CuspVerticalSeedLp N ψ r Y hY)] with z hs hψ hsmul
    simp only [RingHom.id_apply]
    rw [hsmul, hs]
    change _ = c • (gamma0CuspVerticalSeedLp N ψ r Y hY) z
    rw [hψ, gamma0CuspVerticalField_smul]

private theorem vertical_restriction_exists (N : ℕ) [NeZero N]
    (r : SL(2, ℤ)) (Y : ℝ) (hY : 0 < Y) :
    ∃ D : gamma0EnergySpace N →L[ℂ] CuspHyperbolicL2 (N : ℝ) Y,
      ∀ ψ, D (gamma0EnergyTestLinear N ψ) = gamma0CuspVerticalSeedLinear N r Y hY ψ := by
  obtain ⟨C, _, hb⟩ := gamma0CuspVerticalSeedLp_bound N r Y hY
  exact exists_bounded_extension_of_dense_functions (D := h2SmoothCompactSeeds)
    (gamma0CuspVerticalSeedLinear N r Y hY) (gamma0EnergyTestLinear N) (gamma0EnergyTest_dense N)
    (gamma0CuspVerticalSeedLinear N r Y hY).map_add (gamma0CuspVerticalSeedLinear N r Y hY).map_smul
    (gamma0EnergyTestLinear N).map_add (gamma0EnergyTestLinear N).map_smul ⟨C, hb⟩

def gamma0CuspVerticalRestriction (N : ℕ) [NeZero N]
    (r : SL(2, ℤ)) (Y : ℝ) (hY : 0 < Y) :
    gamma0EnergySpace N →L[ℂ] CuspHyperbolicL2 (N : ℝ) Y :=
  (vertical_restriction_exists N r Y hY).choose

theorem gamma0CuspVerticalRestriction_apply (N : ℕ) [NeZero N]
    (r : SL(2, ℤ)) (Y : ℝ) (hY : 0 < Y) (ψ : h2SmoothCompactSeeds) :
    gamma0CuspVerticalRestriction N r Y hY (gamma0EnergyTest N ψ) =
      gamma0CuspVerticalSeedLp N ψ r Y hY :=
  (vertical_restriction_exists N r Y hY).choose_spec ψ

theorem gamma0CuspVerticalRestriction_seed_ae (N : ℕ) [NeZero N]
    (r : SL(2, ℤ)) (Y : ℝ) (hY : 0 < Y) (ψ : h2SmoothCompactSeeds) :
    gamma0CuspVerticalRestriction N r Y hY (gamma0EnergyTest N ψ)
      =ᵐ[volume.restrict (hyperbolicCuspStrip (N : ℝ) Y)] gamma0CuspVerticalField N ψ r := by
  rw [gamma0CuspVerticalRestriction_apply]
  exact gamma0CuspVerticalSeedLp_ae N ψ r Y hY

theorem gamma0CuspVerticalRestriction_bound (N : ℕ) [NeZero N]
    (r : SL(2, ℤ)) (Y : ℝ) (hY : 0 < Y) :
    ∃ C > 0, ∀ u : gamma0EnergySpace N,
      ‖gamma0CuspVerticalRestriction N r Y hY u‖ ≤ C * ‖u‖ := by
  obtain ⟨C, hC, hb⟩ := gamma0CuspVerticalSeedLp_bound N r Y hY
  refine ⟨C, hC, fun u => ?_⟩
  apply isClosed_property (gamma0EnergyTest_dense N)
    (isClosed_le (gamma0CuspVerticalRestriction N r Y hY).continuous.norm
      (continuous_const.mul continuous_norm))
  intro ψ
  change ‖gamma0CuspVerticalRestriction N r Y hY (gamma0EnergyTest N ψ)‖ ≤
    C * ‖gamma0EnergyTest N ψ‖
  rw [gamma0CuspVerticalRestriction_apply]
  exact hb ψ

end ArtinMatthews
