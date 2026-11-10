module

public import ArtinMatthews.SourcePoissonPrimalDualAssembly
public import ArtinMatthews.SourcePoissonActualFiniteFourier
public import ArtinMatthews.SourcePoissonPrimalAbsolute
public import ArtinMatthews.SourcePrimeNormSummability
public import ArtinMatthews.SourceSLocalExponentPoisson
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
open NumberField IsDedekindDomain AllowedGenerators SIntegerPrincipalization StandardAdelic
open SourcePhysical VaryingKummerAnalytic QuadraticWeil
open scoped NumberField Classical
noncomputable section

variable (F : Type) [Field F] [NumberField F] [IsTotallyComplex F]
variable (S₀ : Finset (HeightOneSpectrum (𝓞 F))) {ζ : F} (hζ : IsPrimitiveRoot ζ 12)
variable {J : Ideal (𝓞 F)} (η : EvenIdealRayCharacter F J)
local notation "S" => sourceHilbertSet F S₀
local notation "T" => sourceHilbertSeed F S₀
local notation "R" => sourceRing F S₀
local notation "a" => sourcePrimeExponentGenerator F hζ S₀
local notation "q" => sourcePrimeExponentNorm F S₀
local notation "E" => SourcePrimeExponents F S₀

theorem sourcePoissonPrimalBlock_eq_actualDual
    (hBad : standardWeilBadPlaces F ⊆ sourceHilbertSet F S₀)
    {X : ℝ} (hX : 0 < X) (t : SNormOne F S) (s A : E) :
    sourcePoissonPrimalBlock F S₀ hζ s A t ((q s : ℝ) * X) =
      ((((q s : ℝ) * X) / ((q s : ℝ) * (q A : ℝ)) : ℝ) : ℂ) *
      (Real.sqrt (q s : ℝ) : ℂ) *
        ∑' h : R, sourcePoissonFiniteDualValue F S₀ hζ X t s A h := by
  let d : SWholeUnits F S := (t : SWholeUnits F S) *
    sLocalPositiveScaling F hζ S ((q s : ℝ) * X)
  let w := sourcePoissonNormalizedQuotientWeight F S₀ hζ s A
  let v := sourcePoissonNestedDualTransform F S₀ hζ X t s A
  let D (h : R) := sourcePrincipalQuotientFourier F T (a s * a A)
    (sourcePoissonProductGenerator_ne_zero F S₀ hζ s A) w h
  let j : ℂ := (Real.sqrt (q s : ℝ) : ℂ)
  have htrace : traceBadPlaces F ⊆ S := fun _ hp => hBad (Finset.mem_union_left _ hp)
  have hPrim :
      sourcePoissonPrimalBlock F S₀ hζ s A t ((q s : ℝ) * X) =
      ((sLocalNorm F S d : ℂ) / ((q s : ℂ) * (q A : ℂ))) * ∑' h : R, v h * D h :=
    sourceSLocalExponentPeriodicPoisson F S₀ hζ htrace s A w d
  have hqs : 0 < (q s : ℝ) := Nat.cast_pos.mpr (sourcePrimeExponentNorm_pos F S₀ s)
  have hd : sLocalNorm F S d = (q s : ℝ) * X := by
    dsimp only [d]
    rw [sLocalNorm_mul, show sLocalNorm F S (t : SWholeUnits F S) = 1 from t.property,
      sLocalPositiveScaling_norm F hζ S (mul_pos hqs hX), one_mul]
  have hRatio : ((sLocalNorm F S d : ℂ) / ((q s : ℂ) * (q A : ℂ))) =
      ((((q s : ℝ) * X) / ((q s : ℝ) * (q A : ℝ)) : ℝ) : ℂ) := by
    simp only [hd, Complex.ofReal_div, Complex.ofReal_mul, Complex.ofReal_natCast]
  have hD (h : R) :
      D h = j * sourceExponentFiniteF F hζ S₀ (reflectionPrimeCharacters F hζ S₀) s A h :=
    sourcePoissonQuotientFourier_eq_actual F S₀ hζ hBad s A h
  have hSum : (∑' h : R, v h * D h) =
      j * ∑' h : R, sourcePoissonFiniteDualValue F S₀ hζ X t s A h := by
    calc
      _ = ∑' h : R, j * sourcePoissonFiniteDualValue F S₀ hζ X t s A h := by
        apply tsum_congr
        intro h
        rw [hD, sourcePoissonFiniteDualValue]
        dsimp only [v]
        ac_rfl
      _ = _ := tsum_mul_left
  rw [hPrim, hRatio, hSum, mul_assoc]

/-- The physical density is exactly the nested literal dual density,
with every original lattice and quotient normalization discharged. -/
theorem sourcePoissonOriginalDensity_eq_nestedDual
    (hBad : standardWeilBadPlaces F ⊆ sourceHilbertSet F S₀)
    {X Z : ℝ} (hX : 0 < X) (Y : ℝ) (hZ : 0 < Z) (t : SNormOne F S) :
    sourcePoissonOriginalDensity F S₀ hζ η hBad X Y Z t =
      sourcePoissonNestedDualDensity F S₀ hζ hBad η X Y Z t :=
  (sourcePoissonOriginalDensity_eq_primalExpanded_actual F S₀ hζ η hBad X Y Z hZ t).trans
    (sourcePoissonPrimalExpandedDensity_eq_nestedDual_of_blocks F S₀ hζ η hBad hX Y Z t
      (sourcePoissonPrimalBlock_eq_actualDual F S₀ hζ hBad hX t))

end
end ArtinMatthews.SourceEulerAssembly
