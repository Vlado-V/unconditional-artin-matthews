module

public import ArtinMatthews.SourcePoissonProbeWeightSeparation
public import ArtinMatthews.StandardLocalBall
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

namespace ArtinMatthews.SourcePhysical
open NumberField IsDedekindDomain
open scoped NumberField
noncomputable section

variable (K : Type) [Field K] [NumberField K]
variable (S : Finset (HeightOneSpectrum (𝓞 K)))

theorem sourceSLocalUnitAdditivePoint_continuous : Continuous (sourceSLocalUnitAdditivePoint K S) := by
  apply Continuous.prodMk
  · exact continuous_pi fun w => Units.continuous_val.comp ((continuous_apply w).comp continuous_fst)
  · exact continuous_pi fun p => Units.continuous_val.comp ((continuous_apply p).comp continuous_snd)

end
end ArtinMatthews.SourcePhysical

namespace ArtinMatthews.SourceEulerAssembly
open NumberField IsDedekindDomain AllowedGenerators SourcePhysical Set
open scoped NumberField Classical
noncomputable section

variable (F : Type) [Field F] [NumberField F]
variable (S₀ : Finset (HeightOneSpectrum (𝓞 F))) {ζ : F} (hζ : IsPrimitiveRoot ζ 12)
local notation "S" => sourceHilbertSet F S₀
local notation "R" => sourceRing F S₀
local notation "A" => SLocalAdditiveCompletionSpace F S

/-- The shared compact row box incorporates the actual bounded quotient representatives. -/
def sourcePoissonLogRowBox : Set A :=
  (fun p : SNormOne F S × A => sourceSLocalUnitAdditivePoint F S (p.1 : SWholeUnits F S) * p.2) ''
    (sNormOneCover F S ×ˢ sourceProbeEnlargedAnnulus F hζ S)

variable [IsTotallyComplex F]

theorem sourcePoissonLogRowBox_isCompact : IsCompact (sourcePoissonLogRowBox F S₀ hζ) :=
  ((sNormOneCover_isCompact F S).prod (sourceProbeEnlargedAnnulus_isCompact F hζ S)).image
    (((sourceSLocalUnitAdditivePoint_continuous F S).comp
      (continuous_subtype_val.comp continuous_fst)).mul continuous_snd)

omit [IsTotallyComplex F] in
theorem sourcePoissonOriginalLogPoint_unscale (X Y : ℝ) (t : SNormOne F S) (m : R) :
    sourceSLocalUnitAdditivePoint F S (sLocalPositiveScaling F hζ S (X * Y)) *
        (sourceSLocalUnitAdditivePoint F S (t : SWholeUnits F S) *
          sourcePoissonOriginalLogPoint F S₀ hζ X Y t m) =
      sLocalRingDiagonal F S (m : F) := by
  let ell := sLocalPositiveScaling F hζ S (X * Y)
  let u := (t : SWholeUnits F S) * ell
  change sourceSLocalUnitAdditivePoint F S ell *
    (sourceSLocalUnitAdditivePoint F S (t : SWholeUnits F S) *
      (sLocalRingDiagonal F S (m : F) * sourceSLocalUnitAdditivePoint F S u⁻¹)) = _
  calc
    _ = sLocalRingDiagonal F S (m : F) *
        ((sourceSLocalUnitAdditivePoint F S (t : SWholeUnits F S) *
          sourceSLocalUnitAdditivePoint F S ell) * sourceSLocalUnitAdditivePoint F S u⁻¹) := by ac_rfl
    _ = _ := by
      rw [← sourceSLocalUnitAdditivePoint_mul, ← sourceSLocalUnitAdditivePoint_mul]
      change sLocalRingDiagonal F S (m : F) * sourceSLocalUnitAdditivePoint F S (u * u⁻¹) = _
      rw [mul_inv_cancel, show sourceSLocalUnitAdditivePoint F S 1 = 1 from rfl, mul_one]

omit [IsTotallyComplex F] in
theorem sourcePoissonOriginalLogPoint_mem_scaledBox {X Y : ℝ} {t : SNormOne F S}
    (ht : t ∈ sNormOneFundamentalSet F S) {m : R}
    (hm : sourcePoissonOriginalLogPoint F S₀ hζ X Y t m ∈ sourceProbeEnlargedAnnulus F hζ S) :
    sLocalRingDiagonal F S (m : F) ∈
      (fun y => sourceSLocalUnitAdditivePoint F S (sLocalPositiveScaling F hζ S (X * Y)) * y) ''
        sourcePoissonLogRowBox F S₀ hζ := by
  refine ⟨_, ⟨(t, sourcePoissonOriginalLogPoint F S₀ hζ X Y t m), ?_, rfl⟩,
    sourcePoissonOriginalLogPoint_unscale F S₀ hζ X Y t m⟩
  exact ⟨(sNormOneFundamentalSet_spec F S).2.1 ht, hm⟩

theorem sourcePoissonPhysicalAdditiveFactor_zero_outside_scaledBox {X Y : ℝ}
    (hX : 0 < X) (hY : 0 < Y) {t : SNormOne F S} (ht : t ∈ sNormOneFundamentalSet F S)
    {m : R} (hm : sLocalRingDiagonal F S (m : F) ∉
      (fun y => sourceSLocalUnitAdditivePoint F S (sLocalPositiveScaling F hζ S (X * Y)) * y) ''
        sourcePoissonLogRowBox F S₀ hζ) :
    sourcePoissonPhysicalAdditiveFactor F S₀ hζ X Y t m = 0 :=
  sourcePoissonPhysicalAdditiveFactor_zero_off_logAnnulus F S₀ hζ hX hY t m
    (fun hy => hm (sourcePoissonOriginalLogPoint_mem_scaledBox F S₀ hζ ht hy))

end
end ArtinMatthews.SourceEulerAssembly
