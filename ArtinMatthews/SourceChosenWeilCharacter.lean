module

public import ArtinMatthews.SourceWeilSquareImage
public import ArtinMatthews.SLocalAnalyticWeilCharacter
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
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

/-! The actual analytic Weil character on the one chosen paper B6. -/
namespace ArtinMatthews
open NumberField IsDedekindDomain
open QuadraticWeil AllowedGenerators
open scoped NumberField Classical
noncomputable section
variable (K : Type) [Field K] [NumberField K] [IsTotallyComplex K]
variable {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
variable (S₀ : Finset (HeightOneSpectrum (𝓞 K)))
    (hS : standardWeilBadPlaces K ⊆ sourceHilbertSet K S₀)

def sourceChosenWeilCharacter : chosenB K hζ S₀ →* ℂˣ :=
  (sLocalAnalyticWeilCharacter K (sourceHilbertSet K S₀) hS
    (chosenB_squareImage K hζ S₀) (chosenB_squareImage_isotropic_all K hζ S₀)).comp
      (chosenB_squareImageHom K hζ S₀)

theorem sourceChosenWeilCharacter_apply (b : chosenB K hζ S₀) :
    (sourceChosenWeilCharacter K hζ S₀ hS b : ℂ) =
      sLocalAnalyticWeil K (sourceHilbertSet K S₀)
        (sourceRingSquareMap K (sourceHilbertSet K S₀) b.val) := rfl

theorem sourceChosenWeilCharacter_sq (b : chosenB K hζ S₀) :
    sourceChosenWeilCharacter K hζ S₀ hS b ^ 2 = 1 :=
  sLocalAnalyticWeilCharacter_sq K (sourceHilbertSet K S₀) hS
    (chosenB_squareImage K hζ S₀) (chosenB_squareImage_isotropic_all K hζ S₀)
    (chosenB_squareImageHom K hζ S₀ b)

theorem sourceChosenWeilCharacter_source_value (b : chosenB K hζ S₀) :
    (sLocalAnalyticWeil K (sourceHilbertSet K S₀)
      ((sourceRingSquareMap K (sourceHilbertSet K S₀) b.val)⁻¹))⁻¹ =
      (sourceChosenWeilCharacter K hζ S₀ hS b : ℂ) :=
  sLocalAnalyticWeilCharacter_source_value K (sourceHilbertSet K S₀) hS
    (chosenB_squareImage K hζ S₀) (chosenB_squareImage_isotropic_all K hζ S₀)
    (chosenB_squareImageHom K hζ S₀ b)

end
end ArtinMatthews
