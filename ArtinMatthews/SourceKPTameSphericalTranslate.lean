module

public import ArtinMatthews.SourceKPTameParametric
public import ArtinMatthews.SourceKPProjectiveCanonicalFactors
public import ArtinMatthews.SourceKPProjectiveSections
public import ArtinMatthews.SourceKPTameParametricAction
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

/-! Exact right translates of the genuine parameter-dependent
spherical section on the open Bruhat cell. The central phase and
the inverse torus argument remain explicit. -/

namespace ArtinMatthews
open NumberField IsDedekindDomain StandardAdelic QuadraticWeil AllowedGenerators
open scoped NumberField
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
    (S₀ : Finset (HeightOneSpectrum (𝓞 K))) (P : SourceExteriorPrime K S₀)

local notation "L" => P.val.adicCompletion K
local notation "G₀" => SourceFiniteKP2Projective K hζ P.val
local notation "π₀" => sourceKPTameExteriorUniformizer K hζ S₀ P
local notation "hπ₀" => sourceKPTameExteriorUniformizer_valuation K hζ S₀ P
local notation "h₆" => source_exterior_six_not_mem K S₀ P.val P.property
local notation "l₀" => sourceFiniteKP2ProjectiveLift K hζ P.val
local notation "n₀" => fun x : L => l₀ (sourceGL2Upper x)
local notation "a₀" => fun y : Lˣ => l₀ (sourceGL2Diagonal y)
local notation "w₀" => l₀ sourceGL2Weyl
local notation "κ₀" => sourceFiniteKP2ProjectiveCompactSection K hζ P.val h₆
local notation "z₀" => sourceFiniteKP2ProjectiveCenter K hζ P.val
local notation "τ₀" => sourceKPTameParametricBorelRepresentation K hζ P.val h₆ π₀ hπ₀

def sourceKPTameSphericalPlainIntegrand (s : ℂ) (g : G₀) (x : L) : ZMod 3 → ℂ :=
  (sourceKPTameParametricSphericalSection K hζ P.val h₆ π₀ hπ₀ s).val ((w₀ * n₀ x) * g)

local notation "F₀" => sourceKPTameSphericalPlainIntegrand K hζ S₀ P

theorem sourceKPTameSphericalPlainIntegrand_compact (s : ℂ) (g : G₀)
    (k : SourceFiniteKP2Integral K P.val) (x : L) :
    F₀ s (g * κ₀ k) x = F₀ s g x := by
  unfold sourceKPTameSphericalPlainIntegrand
  rw [← mul_assoc, sourceKPTameParametricSpherical_eval_right]

theorem sourceKPTameSphericalPlainIntegrand_center (s : ℂ) (g : G₀)
    (z : rootsOfUnity 3 L) (x : L) :
    F₀ s (z₀ z * g) x = (sourceKPCentralComplex K hζ P.val z : ℂ) • F₀ s g x := by
  unfold sourceKPTameSphericalPlainIntegrand
  rw [← mul_assoc, (sourceFiniteKP2ProjectiveCenter_commute K hζ P.val z (w₀ * n₀ x)).eq.symm,
    mul_assoc, sourceKPTameParametricSpherical_center]

theorem sourceKPTameSphericalPlainIntegrand_upper (s : ℂ) (g : G₀) (u x : L) :
    F₀ s (n₀ u * g) x = F₀ s g (x + u) := by
  unfold sourceKPTameSphericalPlainIntegrand
  rw [← mul_assoc, mul_assoc w₀, sourceFiniteKP2ProjectiveLift_upper_add]

theorem sourceKPTameSphericalPlainIntegrand_diagonal (s : ℂ) (y : Lˣ) (x : L) :
    F₀ s (a₀ y) x =
      τ₀ s (sourceFiniteKPProjectiveBorelDiagonal K hζ P.val y⁻¹) (F₀ s 1 (x / (y : L))) := by
  unfold sourceKPTameSphericalPlainIntegrand
  rw [mul_one, mul_assoc, sourceFiniteKP2ProjectiveLift_upper_diagonal,
    ← mul_assoc, sourceFiniteKP2ProjectiveLift_weyl_diagonal, mul_assoc,
    ← sourceFiniteKPProjectiveBorelDiagonal_val,
    sourceKPTameParametricSpherical_covariant]

theorem sourceKPTameSphericalPlainIntegrand_iwasawa (s : ℂ) (g : G₀)
    (z : rootsOfUnity 3 L) (u : L) (y : Lˣ) (k : SourceFiniteKP2Integral K P.val)
    (hg : g = z₀ z * n₀ u * a₀ y * κ₀ k) (x : L) :
    F₀ s g x =
      (sourceKPCentralComplex K hζ P.val z : ℂ) •
        τ₀ s (sourceFiniteKPProjectiveBorelDiagonal K hζ P.val y⁻¹)
          (F₀ s 1 ((x + u) / (y : L))) := by
  rw [hg, sourceKPTameSphericalPlainIntegrand_compact,
    mul_assoc (z₀ z) (n₀ u) (a₀ y), sourceKPTameSphericalPlainIntegrand_center,
    sourceKPTameSphericalPlainIntegrand_upper, sourceKPTameSphericalPlainIntegrand_diagonal]

end
end ArtinMatthews
