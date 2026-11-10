module

public import ArtinMatthews.PrincipalAngularCorrection
public import ArtinMatthews.SourceReflectionRowClass
public import ArtinMatthews.SourceKPPositivePhysicalBranchGaussian
public import ArtinMatthews.SourceKPReflectedBranchGaussian
public import ArtinMatthews.SourceReflectionBranchAssembly
public import ArtinMatthews.SourceReflectionBranchProduct
public import ArtinMatthews.SourceReflectionLiteralData
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

/-! The actual source coefficient has the literal reflected expansion
on the original completed Hilbert set. -/
namespace ArtinMatthews

open NumberField IsDedekindDomain QuadraticWeil VaryingKummerAnalytic AllowedGenerators
open SourceEulerAssembly SourcePhysical
open scoped NumberField Classical BigOperators
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K}
variable (hζ : IsPrimitiveRoot ζ 12)
variable (S₀ : Finset (HeightOneSpectrum (𝓞 K)))
local notation "S" => sourceHilbertSet K S₀
local notation "X" => ExteriorUnitSixthClasses (K := K) S
local notation "Q" => SWholePowerClasses K 6 S

theorem sourceReflectionLiteralExpansion_actual
    (hS : standardWeilBadPlaces K ⊆ S) {J : Ideal (𝓞 K)}
    (η : EvenIdealRayCharacter K J) (hJ : J ≠ ⊥)
    (hcut : principalAngularCutoff K J ⊆ S) :
    letI : IsTotallyComplex K := source_isTotallyComplex K hζ
    ∃ (U : Type) (_ : Fintype U)
      (A : X → SourceReflectionExpansionData K S₀ U),
      SourceReflectionLiteralExpansion K S₀ hζ η hS A := by
  letI : IsTotallyComplex K := source_isTotallyComplex K hζ
  let T : ℝ := 3
  have hT : 2 < T := by norm_num [T]
  obtain ⟨p⟩ := sourceKPPositiveSeedData_nonempty K hζ S₀ hS hJ hT
  let v := Classical.choice (inferInstance : Nonempty (InfinitePlace K))
  let L := SourceKPReflectedRetainedLabel K hζ S₀ p.R p.M
  let U := SourceReflectionActualBranchLabel K hζ S₀ p.R p.M
  letI : Fintype X := Fintype.ofFinite X
  letI : Fintype L := sourceKPReflectedRetainedLabel_fintype K hζ S₀ p.R p.M
  letI : Fintype Q := sourceReflectionSixthClassFintype K S₀ hζ
  letI : Fintype U := show Fintype (X × L) from inferInstance
  let A (u : X) := sourceReflectionLiteralActualData K hζ S₀ hS η hJ hT p u v
  let B := sourceKPPositivePhysicalBranchGaussian K hζ S₀ hS η hJ hcut v hT p
  refine ⟨U × Q × Q, inferInstance,
    fun u => sourceReflectionExpansionData_withClassSlices K S₀ hζ (A u), ?_⟩
  refine sourceReflectionLiteralExpansion_of_supportedBranches K S₀ hζ η hS A B ?_ ?_ ?_ ?_
  · intro Z hZ e u
    exact sourceKPPositivePhysicalBranchGaussian_sum K hζ S₀ hS η hJ hcut v hT p hZ e u
  · intro Z _ e u g hg hbad
    exact sourceKPPositivePhysicalBranchGaussian_eq_zero K hζ S₀ hS η hJ hcut v hT p Z e u g hg hbad
  · intro Z hZ e u f hf
    let h := sourceReflectionPowerfulPart e
    let d := sourceReflectionSimplePart e
    have hd := sourceReflectionSimplePart_squarefree e
    have hdh := (sourceReflectionPowerfulSimple_disjoint e).symm
    have he : h + d = e := sourceReflectionPowerfulSimple_add e
    rw [← sourceReflectionSupportedBranch_tsum_prod K S₀ hζ (A u) hZ h d f]
    have hb := sourceKPReflectedBranch_gaussian K hζ S₀ hS η hJ hcut v hT p h d f hf hd hdh u hZ
    change B Z (h + d) u (f ∪ d.support) = _ at hb
    rw [he] at hb
    refine hb.trans (tsum_congr ?_)
    intro j
    exact (sourceReflectionLiteralActualData_term K hζ S₀ hS η hJ hT p u v Z h d f j.1.val j.2).symm
  · intro Z _ e u f _ i hi j
    exact sourceReflectionLiteralActualData_term_zero K hζ S₀ hS η hJ hT p u v
      Z (sourceReflectionPowerfulPart e) (sourceReflectionSimplePart e) f i j hi

end
end ArtinMatthews
