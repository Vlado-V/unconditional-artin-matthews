module

public import ArtinMatthews.SourceChosenWeilCharacter
public import ArtinMatthews.HeckeExtension.SourceSupportedRay
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

/-! The paper's actual analytic Weil S-product extends to a genuine
quadratic Hecke ray character, with literal S-supported conductor bound. -/
namespace ArtinMatthews
open NumberField IsDedekindDomain FractionalIdeal
open QuadraticWeil AllowedGenerators VaryingKummerAnalytic
open scoped NumberField Classical nonZeroDivisors
noncomputable section
variable (K : Type) [Field K] [NumberField K] [IsTotallyComplex K]
variable {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
variable (S₀ : Finset (HeightOneSpectrum (𝓞 K)))
    (hS : standardWeilBadPlaces K ⊆ sourceHilbertSet K S₀)

def sourceAnalyticWeilHeckeCharacter :
    EvenIdealRayCharacter K (sixthKummerFixedIdeal (sourceHilbertSet K S₀)) :=
  sourceSupportedRayCharacter K hζ S₀ (sourceChosenWeilCharacter K hζ S₀ hS)
    (sourceChosenWeilCharacter_sq K hζ S₀ hS)

theorem sourceAnalyticWeilHeckeCharacter_sq (I : FractionalIdealGroup K) :
    (sourceAnalyticWeilHeckeCharacter K hζ S₀ hS).idealHom I ^ 2 = 1 :=
  sourceComplementGlobalIdealCharacter_sq K hζ S₀
    (sourceChosenWeilCharacter K hζ S₀ hS) (sourceChosenWeilCharacter_sq K hζ S₀ hS) I

theorem sourceAnalyticWeilHeckeCharacter_allowed
    (a : allowedSubgroup K hζ S₀) :
    ((sourceAnalyticWeilHeckeCharacter K hζ S₀ hS).idealHom
        (toPrincipalIdeal (𝓞 K) K a.val) : ℂ) =
      (sLocalAnalyticWeil K (sourceHilbertSet K S₀)
        (sLocalGlobalClassMap K 2 (sourceHilbertSet K S₀) a.val⁻¹))⁻¹ := by
  have hi := sourceSupportedRayCharacter_allowed K hζ S₀
    (sourceChosenWeilCharacter K hζ S₀ hS) (sourceChosenWeilCharacter_sq K hζ S₀ hS) a
  have hw := sourceChosenWeilCharacter_source_value K hζ S₀ hS
    ⟨sLocalRingGlobalClassMap K 6 (sourceHilbertSet K S₀) a.val, a.property⟩
  rw [sourceRingSquareMap_global, ← map_inv] at hw
  exact (congrArg Units.val hi).trans hw.symm

omit [IsTotallyComplex K] in
theorem exists_sourceAnalyticWeilHeckeCharacter
    (T : Finset (HeightOneSpectrum (𝓞 K))) :
    ∃ S₀ : Finset (HeightOneSpectrum (𝓞 K)), T ⊆ S₀ ∧
      ∃ Ψ : EvenIdealRayCharacter K (sixthKummerFixedIdeal (sourceHilbertSet K S₀)),
        (∀ I : FractionalIdealGroup K, Ψ.idealHom I ^ 2 = 1) ∧
        ∀ a : allowedSubgroup K hζ S₀,
          (Ψ.idealHom (toPrincipalIdeal (𝓞 K) K a.val) : ℂ) =
            (sLocalAnalyticWeil K (sourceHilbertSet K S₀)
              (sLocalGlobalClassMap K 2 (sourceHilbertSet K S₀) a.val⁻¹))⁻¹ := by
  let := source_isTotallyComplex K hζ
  let S₀ := standardWeilBadPlaces K ∪ T
  have hbad : standardWeilBadPlaces K ⊆ sourceHilbertSet K S₀ :=
    Finset.Subset.trans Finset.subset_union_left (required_subset_sourceHilbertSet K S₀)
  exact ⟨S₀, Finset.subset_union_right, sourceAnalyticWeilHeckeCharacter K hζ S₀ hbad,
    sourceAnalyticWeilHeckeCharacter_sq K hζ S₀ hbad,
    sourceAnalyticWeilHeckeCharacter_allowed K hζ S₀ hbad⟩

end
end ArtinMatthews
