module

public import ArtinMatthews.SourcePoissonOriginalProbe
public import ArtinMatthews.SourceSixthUnitResidue
public import ArtinMatthews.SourceFrequencyNormOneAction
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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

namespace ArtinMatthews.SourceEulerAssembly
open NumberField IsDedekindDomain AllowedGenerators SIntegerPrincipalization SourcePhysical
open scoped NumberField Classical
noncomputable section

variable (F : Type) [Field F] [NumberField F]
variable (S₀ : Finset (HeightOneSpectrum (𝓞 F))) {ζ : F} (hζ : IsPrimitiveRoot ζ 12)
local notation "S" => sourceHilbertSet F S₀
local notation "R" => sourceRing F S₀

/-- The actual source-ring unit used to reindex (m) when a norm-one
representative is multiplied by a diagonal S-unit sixth power. -/
def sourcePoissonPrimalUnit (u : SUnitGroup (K := F) S) : Rˣ :=
  sourceExteriorUnitToSourceUnits F S₀ (sourceActualSUnitToExteriorUnit F S u)

theorem sourcePoissonPrimalUnit_coe (u : SUnitGroup (K := F) S) :
    ((sourcePoissonPrimalUnit F S₀ u : R) : F) = ((u : Fˣ) : F) := rfl

theorem sourcePoissonUnitPoint_diagonal (u : Fˣ) :
    sourceSLocalUnitAdditivePoint F S (sWholeDiagonal F S u) =
      sLocalRingDiagonal F S (u : F) := rfl

/-- The exact argument of the physical probe is unchanged under the paired
sixth-power change of quotient representative and original lattice point. -/
theorem sourcePoissonOriginalTest_mul_sixth (u : SUnitGroup (K := F) S)
    (t : SNormOne F S) (V : ℝ) (m : R) :
    sourcePoissonOriginalTest F S₀ hζ (t * sNormOneSixthMap F S u) V
      (m * (sourcePoissonPrimalUnit F S₀ u : R) ^ 6) =
    sourcePoissonOriginalTest F S₀ hζ t V m := by
  let b : SWholeUnits F S := sWholeDiagonal F S ((u : Fˣ) ^ 6)
  let c : SWholeUnits F S := (t : SWholeUnits F S) * sLocalPositiveScaling F hζ S V
  have hdiag : sLocalRingDiagonal F S (((sourcePoissonPrimalUnit F S₀ u : R) : F) ^ 6) =
      sourceSLocalUnitAdditivePoint F S b := by
    rw [sourcePoissonPrimalUnit_coe F S₀ u]
    exact (sourcePoissonUnitPoint_diagonal F S₀ ((u : Fˣ) ^ 6)).symm
  have htc :
      ((t * sNormOneSixthMap F S u : SNormOne F S) : SWholeUnits F S) *
        sLocalPositiveScaling F hζ S V = c * b := by
    change ((t : SWholeUnits F S) * (sNormOneSixthMap F S u : SWholeUnits F S)) *
      sLocalPositiveScaling F hζ S V = c * b
    rw [sNormOneSixthMap_val F S u]
    dsimp only [b, c]
    ac_rfl
  have hb : b * (c * b)⁻¹ = c⁻¹ := by
    rw [mul_inv_rev, ← mul_assoc, mul_inv_cancel, one_mul]
  unfold sourcePoissonOriginalTest
  rw [Subalgebra.coe_mul, Subalgebra.coe_pow, map_mul, hdiag, htc, mul_assoc,
    ← sourceSLocalUnitAdditivePoint_mul F S, hb]

end
end ArtinMatthews.SourceEulerAssembly
