module

public import ArtinMatthews.SpectralCuspHyperbolicProjection
public import ArtinMatthews.SpectralGamma0CuspPositiveHeightEnergy
public import ArtinMatthews.SpectralGamma0CuspRestriction
public import ArtinMatthews.SpectralCompactDenseCore
public import ArtinMatthews.SpectralGamma0CuspPositiveHeightLp
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

/-! Actual cusp restrictions at every positive height, on the energy completion. -/

noncomputable section
open Set MeasureTheory Filter
open scoped MatrixGroups

namespace ArtinMatthews

def gamma0CuspHeightSeedLp (N : ℕ) [NeZero N] (r : SL(2, ℤ)) (Y : ℝ) (hY : 0 < Y)
    (ψ : h2SmoothCompactSeeds) : CuspHyperbolicL2 (N : ℝ) Y :=
  (gamma0CuspSection_memLp_positive_height N ψ r Y hY).toLp (gamma0CuspSection N ψ r)

theorem gamma0CuspHeightSeedLp_ae (N : ℕ) [NeZero N] (r : SL(2, ℤ)) (Y : ℝ) (hY : 0 < Y)
    (ψ : h2SmoothCompactSeeds) :
    gamma0CuspHeightSeedLp N r Y hY ψ =ᵐ[volume.restrict (hyperbolicCuspStrip (N : ℝ) Y)]
      gamma0CuspSection N ψ r := MemLp.coeFn_toLp (gamma0CuspSection_memLp_positive_height N ψ r Y hY)

def gamma0CuspHeightSeedLinear (N : ℕ) [NeZero N] (r : SL(2, ℤ)) (Y : ℝ) (hY : 0 < Y) :
    h2SmoothCompactSeeds →ₗ[ℂ] CuspHyperbolicL2 (N : ℝ) Y where
  toFun := gamma0CuspHeightSeedLp N r Y hY
  map_add' ψ ξ := by
    apply Lp.ext
    filter_upwards [gamma0CuspHeightSeedLp_ae N r Y hY (ψ+ξ),
      gamma0CuspHeightSeedLp_ae N r Y hY ψ,gamma0CuspHeightSeedLp_ae N r Y hY ξ,
      Lp.coeFn_add (gamma0CuspHeightSeedLp N r Y hY ψ) (gamma0CuspHeightSeedLp N r Y hY ξ)]
      with z hs hψ hξ hadd
    rw [hadd,hs]
    change _ = (gamma0CuspHeightSeedLp N r Y hY ψ) z+(gamma0CuspHeightSeedLp N r Y hY ξ) z
    rw [hψ,hξ]
    change arithmeticPoincareSeed _ (ψ.val+ξ.val) (r⁻¹ • z) = _
    rw [arithmeticPoincareSeed_add]
    rfl
  map_smul' c ψ := by
    apply Lp.ext
    filter_upwards [gamma0CuspHeightSeedLp_ae N r Y hY (c • ψ),
      gamma0CuspHeightSeedLp_ae N r Y hY ψ,
      Lp.coeFn_smul c (gamma0CuspHeightSeedLp N r Y hY ψ)] with z hs hψ hsmul
    simp only [RingHom.id_apply]
    rw [hsmul,hs]
    change _ = c • (gamma0CuspHeightSeedLp N r Y hY ψ) z
    rw [hψ]
    change arithmeticPoincareSeed _ (c • ψ.val) (r⁻¹ • z) = _
    rw [arithmeticPoincareSeed_smul]
    rfl

private theorem height_restriction_seed_bound (N : ℕ) [NeZero N]
    (r : SL(2, ℤ)) (Y : ℝ) (hY : 0 < Y) :
    ∃ C : ℝ, ∀ ψ : h2SmoothCompactSeeds,
      ‖gamma0CuspHeightSeedLinear N r Y hY ψ‖ ≤ C*‖gamma0EnergyTestLinear N ψ‖ := by
  obtain ⟨C,_,hC⟩ := gamma0CuspSection_toLp_positive_height_bound N r Y hY
  exact ⟨C,hC⟩

private theorem height_restriction_exists (N : ℕ) [NeZero N]
    (r : SL(2, ℤ)) (Y : ℝ) (hY : 0 < Y) :
    ∃ R : gamma0EnergySpace N →L[ℂ] CuspHyperbolicL2 (N : ℝ) Y,
      ∀ ψ, R (gamma0EnergyTestLinear N ψ) = gamma0CuspHeightSeedLinear N r Y hY ψ :=
  exists_bounded_extension_of_dense_functions (D := h2SmoothCompactSeeds)
    (gamma0CuspHeightSeedLinear N r Y hY) (gamma0EnergyTestLinear N) (gamma0EnergyTest_dense N)
    (gamma0CuspHeightSeedLinear N r Y hY).map_add (gamma0CuspHeightSeedLinear N r Y hY).map_smul
    (gamma0EnergyTestLinear N).map_add (gamma0EnergyTestLinear N).map_smul
    (height_restriction_seed_bound N r Y hY)

def gamma0CuspHeightRestriction (N : ℕ) [NeZero N]
    (r : SL(2, ℤ)) (Y : ℝ) (hY : 0 < Y) :
    gamma0EnergySpace N →L[ℂ] CuspHyperbolicL2 (N : ℝ) Y :=
  (height_restriction_exists N r Y hY).choose

theorem gamma0CuspHeightRestriction_apply (N : ℕ) [NeZero N]
    (r : SL(2, ℤ)) (Y : ℝ) (hY : 0 < Y) (ψ : h2SmoothCompactSeeds) :
    gamma0CuspHeightRestriction N r Y hY (gamma0EnergyTest N ψ) =
      gamma0CuspHeightSeedLp N r Y hY ψ := (height_restriction_exists N r Y hY).choose_spec ψ

theorem gamma0CuspHeightRestriction_one (N : ℕ) [NeZero N]
    (r : SL(2, ℤ)) (u : gamma0EnergySpace N) :
    gamma0CuspHeightRestriction N r 1 zero_lt_one u = gamma0CuspEnergyRestriction N r u := by
  apply isClosed_property (gamma0EnergyTest_dense N)
    (isClosed_eq (gamma0CuspHeightRestriction N r 1 zero_lt_one).continuous
      (gamma0CuspEnergyRestriction N r).continuous)
  intro ψ
  change gamma0CuspHeightRestriction N r 1 zero_lt_one (gamma0EnergyTest N ψ) =
    gamma0CuspEnergyRestriction N r (gamma0EnergyTest N ψ)
  rw [gamma0CuspHeightRestriction_apply,gamma0CuspEnergyRestriction_apply]
  apply Lp.ext
  exact (gamma0CuspHeightSeedLp_ae N r 1 zero_lt_one ψ).trans (gamma0CuspSeedLp_ae N ψ r).symm

end ArtinMatthews
