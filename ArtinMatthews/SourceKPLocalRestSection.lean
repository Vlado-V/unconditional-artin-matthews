module

public import ArtinMatthews.SourceKPLocalRestCommute
public import ArtinMatthews.SourceKPAdelicCompactSection
public import ArtinMatthews.SourceKPLocalReceiverIntertwining
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

/-! The remaining global factor supplies a genuine local-unit-fixed
vector whenever its projective P-component is the identity. -/

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
local notation "F₀" => sourceKPAdelicCompactSection K hζ s
local notation "ι₀" => sourceKPAdelicLocalProjective K hζ P.val
local notation "σ₀" => sourceKPAdelicLocalBorelRepresentation K hζ P.val s

theorem sourceKPLocalRest_unit_fixed (r : SourceKPAdelicProjective K hζ)
    (hr : sourceKPAdelicLocalBase K hζ P.val r = 1) :
    (F₀).val r ∈ sourceKPLocalUnitFixed K hζ P.val s := by
  intro u hu
  let d := sourceFiniteKPProjectiveBorelDiagonal K hζ P.val u
  let k : SourceFiniteKP2Integral K P.val :=
    ⟨sourceGL2Diagonal u, sourceKPIntegralMatrix_diagonal (sourceKPFiniteVal K P.val) u hu⟩
  have hk : sourceFiniteKP2ProjectiveCompactSection K hζ P.val h₆ k = d.val :=
    congrArg (sourceFiniteKP2ProjectiveMk K hζ P.val)
      (sourceFiniteKP2CompactSection_diagonal K hζ P.val h₆ u hu)
  have hc := sourceKPAdelicLocalProjective_commute_of_base_one K hζ P.val d.val r hr
  calc
    σ₀ d ((F₀).val r) = (F₀).val (ι₀ d.val * r) :=
      (sourceAlgebraicInducedSpace_covariant _ _ F₀
        (sourceKPAdelicLocalBorel K hζ P.val d) r).symm
    _ = (F₀).val (r * ι₀ d.val) := congrArg (F₀).val hc.eq
    _ = (F₀).val (r * ι₀ (sourceFiniteKP2ProjectiveCompactSection K hζ P.val h₆ k)) :=
      congrArg (fun q => (F₀).val (r * ι₀ q)) hk.symm
    _ = (F₀).val r := sourceKPAdelicCompactSection_right_local K hζ P.val h₆ s r k

def sourceKPLocalRestVector (r : SourceKPAdelicProjective K hζ)
    (hr : sourceKPAdelicLocalBase K hζ P.val r = 1) :
    sourceKPLocalUnitFixed K hζ P.val s :=
  ⟨(F₀).val r, sourceKPLocalRest_unit_fixed K hζ S₀ P s r hr⟩

theorem sourceKPLocalRest_section_factor (r : SourceKPAdelicProjective K hζ)
    (hr : sourceKPAdelicLocalBase K hζ P.val r = 1)
    (g : SourceFiniteKP2Projective K hζ P.val)
    (b : SourceFiniteKPProjectiveBorel K hζ P.val) (k : SourceFiniteKP2Integral K P.val)
    (hg : g = b.val * sourceFiniteKP2ProjectiveCompactSection K hζ P.val h₆ k) :
    (F₀).val (ι₀ g * r) = σ₀ b ((F₀).val r) := by
  let q := sourceFiniteKP2ProjectiveCompactSection K hζ P.val h₆ k
  have hc := sourceKPAdelicLocalProjective_commute_of_base_one K hζ P.val q r hr
  calc
    (F₀).val (ι₀ g * r) = (F₀).val (ι₀ b.val * (ι₀ q * r)) := by rw [hg, map_mul, mul_assoc]
    _ = σ₀ b ((F₀).val (ι₀ q * r)) :=
      sourceAlgebraicInducedSpace_covariant _ _ F₀
        (sourceKPAdelicLocalBorel K hζ P.val b) _
    _ = σ₀ b ((F₀).val (r * ι₀ q)) := congrArg (fun a => σ₀ b ((F₀).val a)) hc.eq
    _ = σ₀ b ((F₀).val r) := congrArg (σ₀ b)
      (sourceKPAdelicCompactSection_right_local K hζ P.val h₆ s r k)

theorem sourceKPLocalRest_section (r : SourceKPAdelicProjective K hζ)
    (hr : sourceKPAdelicLocalBase K hζ P.val r = 1)
    (g : SourceFiniteKP2Projective K hζ P.val) :
    (F₀).val (ι₀ g * r) =
      sourceKPLocalReceiverIntertwining K hζ S₀ P s
        (sourceKPLocalRestVector K hζ S₀ P s r hr) ((f₀).val g) := by
  obtain ⟨b, k, hg⟩ := sourceFiniteKP2Projective_Iwasawa K hζ P.val h₆ g
  rw [sourceKPLocalRest_section_factor K hζ S₀ P s r hr g b k hg]
  have hf : (f₀).val g = sourceKPTameParametricBorelRepresentation K hζ P.val h₆ π₀ hπ₀ s b
      (sourceJacquetBasis 0) := by
    rw [hg, sourceKPTameParametricSpherical_covariant K hζ S₀ P,
      sourceKPTameParametricSpherical_compact K hζ S₀ P]
  rw [hf, (sourceKPLocalReceiverIntertwining K hζ S₀ P s
    (sourceKPLocalRestVector K hζ S₀ P s r hr)).isIntertwining,
    sourceKPLocalReceiverIntertwining_zero]
  rfl

end
end ArtinMatthews
