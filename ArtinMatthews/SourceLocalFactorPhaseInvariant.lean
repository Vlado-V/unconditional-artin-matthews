module

public import ArtinMatthews.ProbeIdealSourceWeight
public import ArtinMatthews.SourceEulerLocalTerm
public import ArtinMatthews.SourceCalFEulerProduct
public import ArtinMatthews.SourceLocalTermPhaseInvariant
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
public import Mathlib.Topology.Separation.CompletelyRegular
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! Match the literal local factor to the analytic ideal-prime series,
including the explicit interchange of its two unrestricted degrees. -/
namespace ArtinMatthews.SourceEulerAssembly
open NumberField IsDedekindDomain AllowedGenerators VaryingKummerAnalytic QuadraticWeil
open scoped NumberField Classical BigOperators
noncomputable section
variable (F : Type) [Field F] [NumberField F] [IsTotallyComplex F]
variable {ζ : F} (hζ : IsPrimitiveRoot ζ 12)
variable (S₀ : Finset (HeightOneSpectrum (𝓞 F)))
variable (hS : standardWeilBadPlaces F ⊆ sourceHilbertSet F S₀)
variable {M : Ideal (𝓞 F)} (η : EvenIdealRayCharacter F M)

def sourceSwapOuterInner : (ℕ × ℕ × ℕ) ≃ (ℕ × ℕ × ℕ) where
  toFun a := (a.2.1, a.1, a.2.2)
  invFun a := (a.2.1, a.1, a.2.2)
  left_inv := by rintro ⟨k, l, m⟩; rfl
  right_inv := by rintro ⟨l, k, m⟩; rfl

theorem sourceLocalEulerFactor_eq_ideal_of_summable
    (u : sourceRing F S₀) (hu : u ≠ 0) (ξ w z : ℂ) (P : SourceExteriorPrime F S₀)
    (hs : Summable (sourceLocalEulerTerm F hζ S₀ hS η u hu ξ w z P)) :
    let χ := reflectionPrimeCharacters F hζ S₀ P
    sourceLocalEulerFactor F hζ S₀ hS η u hu ξ w z P =
      probeIdealSourceSeries F P.val χ (sourceElementExponents F S₀ u hu P)
        (probeIdealGaussGamma F P.val χ 2)
        (probeIdealGaussLocalVartheta F P.val χ (η.allCoefficient P.val.asIdeal))
        (sourceResidualCharacterUnit F hζ S₀ u hu P : ℂ) ξ w z := by
  dsimp only
  unfold sourceLocalEulerFactor probeIdealSourceSeries
  rw [hs.tsum_prod, tsum_fintype]
  apply Finset.sum_congr rfl
  intro e _
  calc
    _ = ∑' a : ℕ × ℕ × ℕ, sourceLocalEulerTerm F hζ S₀ hS η u hu ξ w z P
        (e, a.2.1, a.1, a.2.2) :=
      (sourceSwapOuterInner.tsum_eq (fun a => sourceLocalEulerTerm F hζ S₀ hS η u hu ξ w z P (e, a))).symm
    _ = _ := tsum_congr (fun a => sourceLocalEulerTerm_eq_ideal F hζ S₀ hS η P u hu ξ w z
      (e, a.2.1, a.1, a.2.2))

theorem sourceLocalEulerFactor_eq_ideal
    (u : sourceRing F S₀) (hu : u ≠ 0) (ξ w z : ℂ) (P : SourceExteriorPrime F S₀)
    (hξ : 2 < ξ.re) (hw : 2 < w.re) (hz : 1 / 6 < z.re) :
    let χ := reflectionPrimeCharacters F hζ S₀ P
    sourceLocalEulerFactor F hζ S₀ hS η u hu ξ w z P =
      probeIdealSourceSeries F P.val χ (sourceElementExponents F S₀ u hu P)
        (probeIdealGaussGamma F P.val χ 2)
        (probeIdealGaussLocalVartheta F P.val χ (η.allCoefficient P.val.asIdeal))
        (sourceResidualCharacterUnit F hζ S₀ u hu P : ℂ) ξ w z :=
  sourceLocalEulerFactor_eq_ideal_of_summable F hζ S₀ hS η u hu ξ w z P
    (sourceLocalEulerTerm_summable_norm F hζ S₀ hS η u hu ξ w z hξ hw hz P).of_norm

end
end ArtinMatthews.SourceEulerAssembly
