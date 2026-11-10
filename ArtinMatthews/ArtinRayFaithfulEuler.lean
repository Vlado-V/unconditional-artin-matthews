module

public import ArtinMatthews.ArtinAbelianEulerLog
public import ArtinMatthews.ArtinRayNormConductor
public import ArtinMatthews.VaryingKummerAnalyticRayIdealSeries
public import ArtinMatthews.ArtinRayFaithfulEulerLocal
public import ArtinMatthews.VaryingKummerAnalyticRayIdealEuler
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

/-! The exact faithful norm-conductor ray series is the full Artin
Euler product, with all finite local factors retained. -/
namespace ArtinMatthews.VaryingKummerAnalytic.ArtinRay
open NumberField AbelianLocal OAI.PrimeDegreePackets
open scoped NumberField Classical BigOperators
noncomputable section

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L]
variable [Algebra K L] [FiniteDimensional K L] [IsAbelianGalois K L] [IsTotallyComplex K]

theorem abelianNormConductorRayCharacter_dirichlet_eq_artin
    (χ : Gal(L/K) →* ℂˣ) (hχ : Function.Injective χ) {s : ℂ} (hs : 1 < s.re) :
    (abelianNormConductorRayCharacter K L χ).dirichlet s =
      abelianArtinEulerProduct K L χ s := by
  let ψ := abelianNormConductorRayCharacter K L χ
  have hf : (fun p : Nat.Primes => abelianArtinRationalFactor K L χ p s) =
      (fun p : Nat.Primes => ∏ P : idealsOverPrime K (p : ℕ), (1 - ψ.idealTerm hs P.val)⁻¹) := by
    funext p
    unfold abelianArtinRationalFactor
    apply Finset.prod_congr rfl
    intro P _
    rw [ψ.idealTerm_apply hs P.val]
    exact abelianNormConductorRayCharacter_localFactor χ hχ (primeOverHeightOne K p P) s
  have ha := abelianArtinEulerProduct_hasProd K L χ hs
  rw [hf] at ha
  exact (ψ.dirichlet_hasProd hs).unique ha

end
end ArtinMatthews.VaryingKummerAnalytic.ArtinRay
