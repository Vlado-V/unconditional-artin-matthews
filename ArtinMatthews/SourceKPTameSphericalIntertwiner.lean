module

public import ArtinMatthews.SourceKPExteriorScattering
public import ArtinMatthews.SourceKPTameParametric
public import ArtinMatthews.SourceKPExceptionalLocalFactor
public import ArtinMatthews.SourceKPTameIntertwiningAbsolute
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
public import Mathlib.RingTheory.Etale.Weakly
public import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.TotallySplit
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

/-! The actual spherical intertwining integral in the genuine tame
principal series, with the exceptional normalization retained. -/

namespace ArtinMatthews
open NumberField IsDedekindDomain MeasureTheory SourcePhysical StandardAdelic
open AllowedGenerators VaryingKummerAnalytic
open scoped NumberField
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
    (S₀ : Finset (HeightOneSpectrum (𝓞 K))) (P : SourceExteriorPrime K S₀)

local notation "L" => P.val.adicCompletion K
local notation "π₀" => sourceKPTameExteriorUniformizer K hζ S₀ P
local notation "hπ₀" => sourceKPTameExteriorUniformizer_valuation K hζ S₀ P
local notation "h₆" => source_exterior_six_not_mem K S₀ P.val P.property
local notation "l₀" => sourceFiniteKP2ProjectiveLift K hζ P.val
local notation "fₛ[" s "]" => Subtype.val (sourceKPTameParametricSphericalSection K hζ P.val h₆ π₀ hπ₀ s)
local notation "μ₀" => sourceJacquetHaar K P.val

def sourceKPTameSphericalIntertwiner (s : ℂ) : ZMod 3 → ℂ :=
  ∫ x : L, fₛ[s] (l₀ sourceGL2Weyl * l₀ (sourceGL2Upper x)) ∂μ₀

theorem sourceKPTameSphericalIntertwiner_integrable (hP : P.val ∉ traceBadPlaces K)
    {s : ℂ} (hs : 0 < s.re) :
    Integrable (fun x : L => fₛ[s] (l₀ sourceGL2Weyl * l₀ (sourceGL2Upper x))) μ₀ := by
  have he : (fun x : L => fₛ[s] (l₀ sourceGL2Weyl * l₀ (sourceGL2Upper x))) =
      sourceKPTameIntertwiningIntegrand K hζ S₀ P s :=
    funext (sourceKPTameParametricSpherical_open K hζ S₀ P s)
  rw [he]
  exact sourceKPTameIntertwiningIntegrand_integrable K hζ S₀ P hP hs

theorem sourceKPTameSphericalIntertwiner_eq (hP : P.val ∉ traceBadPlaces K)
    {s : ℂ} (hs : 0 < s.re) :
    sourceKPTameSphericalIntertwiner K hζ S₀ P s =
      sourceKPUnramifiedScatteringFactor P.val s • sourceJacquetBasis 0 := by
  unfold sourceKPTameSphericalIntertwiner
  simp_rw [sourceKPTameParametricSpherical_open K hζ S₀ P s]
  exact sourceKPTameIntertwiningIntegral_eq K hζ S₀ P hP hs

theorem sourceKPTameSphericalIntertwiner_exceptional (hP : P.val ∉ traceBadPlaces K) :
    sourceKPTameSphericalIntertwiner K hζ S₀ P (1/6) =
      (1+(Ideal.absNorm P.val.asIdeal : ℂ)⁻¹) • sourceJacquetBasis 0 := by
  rw [sourceKPTameSphericalIntertwiner_eq K hζ S₀ P hP (by norm_num),
    sourceKPUnramifiedScatteringFactor_exceptional]

theorem sourceKPTameSphericalIntertwiner_exceptional_ne_zero (hP : P.val ∉ traceBadPlaces K) :
    sourceKPTameSphericalIntertwiner K hζ S₀ P (1/6) ≠ 0 := by
  rw [sourceKPTameSphericalIntertwiner_eq K hζ S₀ P hP (by norm_num)]
  apply smul_ne_zero (sourceKPUnramifiedScatteringFactor_exceptional_ne_zero P.val)
  intro h
  have hv := congrArg (fun v : ZMod 3 → ℂ => v 0) h
  simp [sourceJacquetBasis] at hv

end
end ArtinMatthews
