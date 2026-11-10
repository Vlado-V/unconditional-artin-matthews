module

public import ArtinMatthews.SourcePoissonNestedDual
public import ArtinMatthews.SourceFrequencyPoissonArgument
public import ArtinMatthews.SourcePoissonActualQuotientUnfold
public import ArtinMatthews.SourceExponentPowers
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
open NumberField IsDedekindDomain AllowedGenerators MeasureTheory SourcePhysical
open VaryingKummerAnalytic QuadraticWeil
open scoped NumberField Classical BigOperators
noncomputable section

variable (F : Type) [Field F] [NumberField F]
variable (S₀ : Finset (HeightOneSpectrum (𝓞 F))) {ζ : F} (hζ : IsPrimitiveRoot ζ 12)
local notation "S" => sourceHilbertSet F S₀
local notation "R" => sourceRing F S₀
local notation "E" => SourcePrimeExponents F S₀
local notation "C" => ReflectionSquarefreeExponents F S₀
local notation "H" => SourceNonzeroFrequency F S₀
local notation "U" => SourceFrequencyRepresentativeIndex F S₀
local notation "I" => SourcePoissonPhysicalOrbitIndex F S₀
local notation "Γ" => sNormOneSixthSubgroup F S
local notation "Γₐ" => SourceExteriorUnitSixthPowers S
local notation "eΓ" => sourceExteriorSixthNormOneEquiv F S
local notation "a" => sourcePrimeExponentGenerator F hζ S₀
local notation "au" => sourcePrimeExponentUnit F hζ S₀
local notation "q" => sourcePrimeExponentNorm F S₀

private def sourcePoissonDualOrbitReorder : I × Γ ≃ E × ((C × E) × (U × (E × Γ))) where
  toFun p := (p.1.2.2.2.1, ((p.1.2.1, p.1.2.2.1), (p.1.1, p.1.2.2.2.2, p.2)))
  invFun d := ((d.2.2.1, (d.2.1.1, d.2.1.2, d.1, d.2.2.2.1)), d.2.2.2.2)
  left_inv _ := rfl
  right_inv _ := rfl

/-- The exact orbit-frequency bijection, with the untouched exterior row indices. -/
def sourcePoissonNestedDualIndexEquiv : I × Γ ≃ SourcePoissonNestedDualIndex F S₀ :=
  let e : U × (E × Γ) ≃ H :=
    ((Equiv.refl U).prodCongr ((Equiv.refl E).prodCongr (eΓ).symm.toEquiv)).trans
      (sourceFrequencyOrbitEquiv F hζ S₀)
  (sourcePoissonDualOrbitReorder F S₀).trans
    ((Equiv.refl E).prodCongr ((Equiv.refl (C × E)).prodCongr e))

theorem sourcePoissonNestedDualIndexEquiv_apply
    (u : U) (c : C) (n s r : E) (γ : Γ) :
    sourcePoissonNestedDualIndexEquiv F S₀ hζ ((u, (c, n, s, r)), γ) =
      (s, ((c, n), sourceFrequencyOrbitEquiv F hζ S₀ (u, r, (eΓ).symm γ))) := rfl

theorem sourcePoissonNestedDualIndexEquiv_apply_orbit
    (u : U) (c : C) (n s r : E) (γ : Γₐ) :
    sourcePoissonNestedDualIndexEquiv F S₀ hζ ((u, (c, n, s, r)), eΓ γ) =
      (s, ((c, n), sourceFrequencyOrbitEquiv F hζ S₀ (u, r, γ))) := by
  rw [sourcePoissonNestedDualIndexEquiv_apply, MulEquiv.symm_apply_apply]

variable [IsTotallyComplex F]
local notation "FourierW₀" => sourceSLocalCompletionFourier F S (sourceSLocalCompletionProbe F S)

/-- The literal completion frequency can be expressed using its genuine field unit. -/
theorem sourcePoissonNestedDualTransform_fieldUnit
    (X : ℝ) (t : SNormOne F S) (s A : E) (h : H) :
    sourcePoissonNestedDualTransform F S₀ hζ X t s A h.val =
      FourierW₀ (sourceSLocalUnitAdditivePoint F S
        (((t : SWholeUnits F S) * sLocalPositiveScaling F hζ S ((q s : ℝ) * X)) *
          sWholeDiagonal F S (sourceNonzeroFrequencyFieldUnit F S₀ h / (au s * au A)))) := by
  have hv : ((sourceNonzeroFrequencyFieldUnit F S₀ h / (au s * au A) : Fˣ) : F) =
      (h.val : F) / ((a s * a A : R) : F) := by
    rw [Units.val_div_eq_div_val, Units.val_mul, sourceNonzeroFrequencyFieldUnit_val,
      sourcePrimeExponentUnit_val, sourcePrimeExponentUnit_val, Subalgebra.coe_mul]
  have hd : sLocalRingDiagonal F S ((h.val : F) / ((a s * a A : R) : F)) =
      sourceSLocalUnitAdditivePoint F S
        (sWholeDiagonal F S (sourceNonzeroFrequencyFieldUnit F S₀ h / (au s * au A))) :=
    congrArg (sLocalRingDiagonal F S) hv.symm
  rw [sourcePoissonNestedDualTransform, hd, ← sourceSLocalUnitAdditivePoint_mul]

theorem sourcePoissonNestedDualTransform_orbit
    (X : ℝ) (t : SNormOne F S) (s A : E) (u : U) (r : E) (γ : Γₐ) :
    sourcePoissonNestedDualTransform F S₀ hζ X t s A
      (sourceFrequencyOrbitEquiv F hζ S₀ (u, r, γ)).val =
      FourierW₀ (sourceSLocalUnitAdditivePoint F S
        ((t : SWholeUnits F S) * (eΓ γ).val.val *
          sourceFrequencyPoissonArgument F hζ S₀ X s A u r)) := by
  rw [sourcePoissonNestedDualTransform_fieldUnit, mul_assoc,
    sourceFrequencyPoissonArgument_orbit, ← mul_assoc]

variable (hBad : standardWeilBadPlaces F ⊆ sourceHilbertSet F S₀)
variable {J : Ideal (𝓞 F)} (η : EvenIdealRayCharacter F J)

/-- The physical scalar is exactly the orbit amplitude at the chosen nonzero representative. -/
theorem sourcePoissonNestedDualScalar_representative
    (X Y Z : ℝ) (s : E) (c : C) (n : E) (u : U) (r : E) :
    sourcePoissonNestedDualScalar F S₀ hζ hBad η X Y Z s c n
      ((sourceFrequencyRepresentative F hζ S₀ u).val * a r ^ 6) =
      sourcePoissonOrbitAmplitude F S₀ hζ hBad η X Y Z
        (sourceFrequencyRepresentative F hζ S₀ u) (c, n, s, r) := by
  unfold sourcePoissonNestedDualScalar sourcePoissonPhysicalGaussianCoefficient
    sourcePoissonOrbitAmplitude sourcePoissonOrbitCoefficient
  dsimp only
  rw [sourcePrimeExponentNorm_squarefree_cube, Nat.cast_mul, Nat.cast_pow]
  simp only [Complex.ofReal_mul, Complex.ofReal_inv, Complex.ofReal_natCast, div_eq_mul_inv, mul_inv]
  ring

end
end ArtinMatthews.SourceEulerAssembly
