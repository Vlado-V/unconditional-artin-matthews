module

public import ArtinMatthews.FiniteSupportEulerPrefix
public import ArtinMatthews.SourceEulerLocalTerm
public import ArtinMatthews.SourceGlobalEulerCoefficients
public import ArtinMatthews.FiniteSupportEuler
public import ArtinMatthews.SourceEulerTermFactorization
public import ArtinMatthews.SourceGlobalEulerMajorant
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

/-! The Euler product of the actual source05 series on its initial
absolute-convergence domain, with the literal local coefficient tables. -/
namespace ArtinMatthews.SourceEulerAssembly
open NumberField IsDedekindDomain AllowedGenerators VaryingKummerAnalytic QuadraticWeil SourceEuler
open scoped NumberField Classical BigOperators
noncomputable section
variable (F : Type) [Field F] [NumberField F] [IsTotallyComplex F]
variable {ζ : F} (hζ : IsPrimitiveRoot ζ 12)
variable (S₀ : Finset (HeightOneSpectrum (𝓞 F)))
variable (hS : standardWeilBadPlaces F ⊆ sourceHilbertSet F S₀)
variable {M : Ideal (𝓞 F)} (η : EvenIdealRayCharacter F M)
variable (u : sourceRing F S₀) (hu : u ≠ 0) (ξ w z : ℂ)
variable (hξ : 2 < ξ.re) (hw : 2 < w.re) (hz : 1 / 6 < z.re)

include hξ hw hz

theorem sourceGlobalEulerChoices_summable_norm :
    Summable (fun a : SourceExteriorPrime F S₀ →₀ SourceLocalChoice =>
      ‖finiteChoiceWeight (sourceLocalEulerTerm F hζ S₀ hS η u hu ξ w z) a‖) := by
  have h := (sourceGlobalCalF_summable_norm F S₀ hζ hS η u ξ w z hξ hw hz).comp_injective
    (sourceCoordinateEquiv (SourceExteriorPrime F S₀)).injective
  exact h.congr (fun a => congrArg norm (sourceGlobalEulerTerm_factor F hζ S₀ hS η u hu ξ w z a))

theorem sourceLocalEulerTerm_summable_norm (P : SourceExteriorPrime F S₀) :
    Summable (fun a : SourceLocalChoice => ‖sourceLocalEulerTerm F hζ S₀ hS η u hu ξ w z P a‖) :=
  localChoice_summable (sourceLocalEulerTerm F hζ S₀ hS η u hu ξ w z)
    (sourceLocalEulerTerm_zero F hζ S₀ hS η u hu ξ w z)
    (sourceGlobalEulerChoices_summable_norm F hζ S₀ hS η u hu ξ w z hξ hw hz) P

theorem sourceGlobalCalF_hasProd :
    HasProd (sourceLocalEulerFactor F hζ S₀ hS η u hu ξ w z)
      (sourceGlobalCalF F hζ S₀ hS η u ξ w z) := by
  have h := finiteChoice_hasProd (sourceLocalEulerTerm F hζ S₀ hS η u hu ξ w z)
    (sourceLocalEulerTerm_zero F hζ S₀ hS η u hu ξ w z)
    (sourceGlobalEulerChoices_summable_norm F hζ S₀ hS η u hu ξ w z hξ hw hz)
  have hs : (∑' a : SourceExteriorPrime F S₀ →₀ SourceLocalChoice,
        finiteChoiceWeight (sourceLocalEulerTerm F hζ S₀ hS η u hu ξ w z) a) =
      sourceGlobalCalF F hζ S₀ hS η u ξ w z := by
    calc
      _ = ∑' a : SourceExteriorPrime F S₀ →₀ SourceLocalChoice,
          sourceGlobalEulerTerm F hζ S₀ hS η u ξ w z
            (sourceCoordinateEquiv (SourceExteriorPrime F S₀) a) :=
        tsum_congr (fun a => (sourceGlobalEulerTerm_factor F hζ S₀ hS η u hu ξ w z a).symm)
      _ = _ := (sourceCoordinateEquiv (SourceExteriorPrime F S₀)).tsum_eq
        (sourceGlobalEulerTerm F hζ S₀ hS η u ξ w z)
  rw [hs] at h
  exact h

theorem sourceGlobalCalF_eq_tprod :
    sourceGlobalCalF F hζ S₀ hS η u ξ w z =
      ∏' P, sourceLocalEulerFactor F hζ S₀ hS η u hu ξ w z P :=
  (sourceGlobalCalF_hasProd F hζ S₀ hS η u hu ξ w z hξ hw hz).tprod_eq.symm

end
end ArtinMatthews.SourceEulerAssembly
