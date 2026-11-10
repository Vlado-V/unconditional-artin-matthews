module

public import ArtinMatthews.SpectralCuspTwoCellHyperbolic
public import ArtinMatthews.SpectralModularDensitySeeds
public import Mathlib.Analysis.CStarAlgebra.Module.Constructions
public import ArtinMatthews.SpectralCuspSmoothUnfolding
public import ArtinMatthews.SpectralModularDensity
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

/-! Compact scalar unfolding for arbitrary completed full-mass vectors.
Continuity is supplied by the actual two-cell restriction operator, not by a
chosen continuous representative of an L² class. -/
namespace ArtinMatthews
open MeasureTheory Set Filter
open scoped MatrixGroups InnerProductSpace
noncomputable section

theorem cuspCompactSeed_memLp (w Y : ℝ) (ψ : h2SmoothCompactSeeds) :
    MemLp (fun z : UpperHalfPlane => ψ.val z) 2
      (volume.restrict (hyperbolicCuspStrip w Y)) :=
  (ψ.val.continuous.memLp_of_hasCompactSupport ψ.val.hasCompactSupport
    (μ := (volume : Measure UpperHalfPlane))).restrict _

def cuspCompactSeedLp (w Y : ℝ) (ψ : h2SmoothCompactSeeds) : CuspHyperbolicL2 w Y :=
  (cuspCompactSeed_memLp w Y ψ).toLp (fun z : UpperHalfPlane => ψ.val z)

theorem cuspCompactSeedLp_inner (w Y : ℝ) (ψ : h2SmoothCompactSeeds)
    (f : CuspHyperbolicL2 w Y) :
    inner ℂ (cuspCompactSeedLp w Y ψ) f =
      ∫ z in hyperbolicCuspStrip w Y, inner ℂ (ψ.val z) (f z) := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [(cuspCompactSeed_memLp w Y ψ).coeFn_toLp] with z hz
  exact congrArg (fun a => inner ℂ a (f z)) hz

theorem gamma0CuspTwoCellMassRestriction_seed_inner (N : ℕ) [NeZero N]
    (r : SL(2, ℤ)) (Y : ℝ) (hY : 0 < Y) (ψ φ : h2SmoothCompactSeeds)
    (hψ : Function.support (fun z : UpperHalfPlane => ψ.val z) ⊆
      hyperbolicCuspStrip (2 * (N : ℝ)) Y) :
    inner ℂ (cuspCompactSeedLp (2 * (N : ℝ)) Y ψ)
      (gamma0CuspTwoCellMassRestriction N r Y hY (gamma0SmoothSeedMass N φ)) =
      ∫ z : UpperHalfPlane, inner ℂ (ψ.val z) (gamma0CuspSection N φ r z) := by
  rw [cuspCompactSeedLp_inner]
  calc
    _ = ∫ z in hyperbolicCuspStrip (2 * (N : ℝ)) Y,
        inner ℂ (ψ.val z) (gamma0CuspSection N φ r z) := by
      apply integral_congr_ae
      filter_upwards [gamma0CuspTwoCellMassRestriction_seed_ae N r Y hY φ] with z hz
      rw [hz]
    _ = _ := setIntegral_eq_integral_of_forall_compl_eq_zero (fun z hz => by
      have hzero : ψ.val z = 0 := Function.notMem_support.mp (fun h => hz (hψ h))
      rw [hzero, inner_zero_left])

/-- The exact completed mass inner product unfolds against its genuine
bounded two-cell cusp restriction, retaining the SL₂ multiplicity two. -/
theorem gamma0Mass_inner_unfold_twoCell (N : ℕ) [NeZero N]
    (r : SL(2, ℤ)) (Y : ℝ) (hY : 0 < Y) (ψ : h2SmoothCompactSeeds)
    (hψ : Function.support (fun z : UpperHalfPlane => ψ.val z) ⊆
      hyperbolicCuspStrip (2 * (N : ℝ)) Y) (f : Gamma0RegionL2 N) :
    inner ℂ (gamma0SmoothSeedMass N (modularTranslateSmoothSeed r ψ)) f =
      2 * inner ℂ (cuspCompactSeedLp (2 * (N : ℝ)) Y ψ)
        (gamma0CuspTwoCellMassRestriction N r Y hY f) := by
  apply isClosed_property (gamma0SmoothSeedMass_denseRange N)
    (isClosed_eq (by fun_prop) (by fun_prop))
  intro φ
  rw [gamma0SmoothSeedMass_inner_unfold_translated,
    gamma0CuspTwoCellMassRestriction_seed_inner N r Y hY ψ φ hψ]

/-- The preceding identity expressed as the literal invariant-measure integral. -/
theorem gamma0Mass_inner_unfold_twoCell_integral (N : ℕ) [NeZero N]
    (r : SL(2, ℤ)) (Y : ℝ) (hY : 0 < Y) (ψ : h2SmoothCompactSeeds)
    (hψ : Function.support (fun z : UpperHalfPlane => ψ.val z) ⊆
      hyperbolicCuspStrip (2 * (N : ℝ)) Y) (f : Gamma0RegionL2 N) :
    inner ℂ (gamma0SmoothSeedMass N (modularTranslateSmoothSeed r ψ)) f =
      2 * ∫ z in hyperbolicCuspStrip (2 * (N : ℝ)) Y,
        inner ℂ (ψ.val z) (gamma0CuspTwoCellMassRestriction N r Y hY f z) := by
  rw [gamma0Mass_inner_unfold_twoCell N r Y hY ψ hψ f, cuspCompactSeedLp_inner]

theorem gamma0Mass_twoCell_pairing_integrable (N : ℕ) [NeZero N]
    (r : SL(2, ℤ)) (Y : ℝ) (hY : 0 < Y) (ψ : h2SmoothCompactSeeds)
    (f : Gamma0RegionL2 N) :
    IntegrableOn (fun z : UpperHalfPlane =>
      inner ℂ (ψ.val z) (gamma0CuspTwoCellMassRestriction N r Y hY f z))
      (hyperbolicCuspStrip (2 * (N : ℝ)) Y) volume := by
  have hi := L2.integrable_inner (𝕜 := ℂ) (cuspCompactSeedLp (2 * (N : ℝ)) Y ψ)
    (gamma0CuspTwoCellMassRestriction N r Y hY f)
  apply hi.congr
  filter_upwards [(cuspCompactSeed_memLp (2 * (N : ℝ)) Y ψ).coeFn_toLp] with z hz
  exact congrArg (fun a => inner ℂ a (gamma0CuspTwoCellMassRestriction N r Y hY f z)) hz

end
end ArtinMatthews
