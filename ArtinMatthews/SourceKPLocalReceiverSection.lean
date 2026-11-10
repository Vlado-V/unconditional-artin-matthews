module

public import ArtinMatthews.SourceKPLocalReceiverIntertwining
public import ArtinMatthews.SourceKPAdelicCompactSection
public import ArtinMatthews.SourceKPTameCompactEmbedding
public import ArtinMatthews.SourceKPTameParametricOpenCell
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

/-! The universal receiver identifies the actual global section on
one local factor with the literal local spherical section. -/

namespace ArtinMatthews
open NumberField IsDedekindDomain
open scoped NumberField AdeleRing
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
    (S₀ : Finset (HeightOneSpectrum (𝓞 K))) (P : SourceExteriorPrime K S₀) (s : ℂ)

local notation "π₀" => sourceKPTameExteriorUniformizer K hζ S₀ P
local notation "hπ₀" => sourceKPTameExteriorUniformizer_valuation K hζ S₀ P
local notation "h₆" => source_exterior_six_not_mem K S₀ P.val P.property
local notation "f₀" => sourceKPTameParametricSphericalSection K hζ P.val h₆ π₀ hπ₀ s

theorem sourceKPLocalSphericalReceiver_section (g : SourceFiniteKP2Projective K hζ P.val) :
    (sourceKPAdelicCompactSection K hζ s).val (sourceKPAdelicLocalProjective K hζ P.val g) =
      sourceKPLocalSphericalReceiver K hζ S₀ P s ((f₀).val g) := by
  obtain ⟨b, k, hg⟩ := sourceFiniteKP2Projective_Iwasawa K hζ P.val h₆ g
  rw [sourceKPAdelicCompactSection_local_factor K hζ P.val h₆ s g b k hg]
  have hf : (f₀).val g = sourceKPTameParametricBorelRepresentation K hζ P.val h₆ π₀ hπ₀ s b
      (sourceJacquetBasis 0) := by
    rw [hg, sourceKPTameParametricSpherical_covariant K hζ S₀ P,
      sourceKPTameParametricSpherical_compact K hζ S₀ P]
  rw [hf, (sourceKPLocalSphericalReceiver K hζ S₀ P s).isIntertwining,
    sourceKPLocalSphericalReceiver_zero]

end
end ArtinMatthews
