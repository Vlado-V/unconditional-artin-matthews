module

public import ArtinMatthews.SourceQuadraticDualFiniteErrors
public import ArtinMatthews.SourceQuadraticRadicalRows
public import ArtinMatthews.SourceQuadraticDualIdealRows
public import ArtinMatthews.SourceQuadraticSmallAmplitude
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

/-! The actual squarefree ideal error on an exact exterior row set,
including each fixed bad divisor and its norm in the contour scale. -/
namespace ArtinMatthews.SourceEulerAssembly
open NumberField IsDedekindDomain StandardAdelic VaryingKummerAnalytic
open scoped NumberField Classical BigOperators
noncomputable section

variable (F : Type) [Field F] [NumberField F] [IsTotallyComplex F]
variable (S₀ : Finset (HeightOneSpectrum (𝓞 F))) {ζ : F} (hζ : IsPrimitiveRoot ζ 12)
local notation "E" => SourcePrimeExponents F S₀
local notation "I" => sourcePrimeExponentIdeal F S₀
local notation "q" => sourcePrimeExponentNorm F S₀
local notation "Bad" => sourceQuadraticBlockBadIdeal F S₀
local notation "C" e:max => sourceQuadraticConductor F S₀ hζ e
local notation "Ψ" => sourceQuadraticRayCharacter F S₀ hζ
local notation "A" => quadraticHeckeFieldScale F
local notation "r" => InfinitePlace.nrComplexPlaces F

def sourceQuadraticDualExteriorRows (K : ℝ) (d : Ideal (𝓞 F)) : Finset E :=
  (sourceQuadraticBlockRadicalRows F S₀ 0 K).filter
    (fun a => (q a : ℝ) * (Ideal.absNorm d : ℝ) ≤ K)

omit [IsTotallyComplex F] in
theorem sourceQuadraticDualExteriorRows_spec (K : ℝ) (d : Ideal (𝓞 F))
    (a : E) (ha : a ∈ sourceQuadraticDualExteriorRows F S₀ K d) :
    sourceReflectionIsSquarefree a ∧ (q a : ℝ) ≤ K ∧
      (q a : ℝ) * (Ideal.absNorm d : ℝ) ≤ K := by
  obtain ⟨ha, hnorm⟩ := Finset.mem_filter.mp ha
  exact ⟨(sourceQuadraticBlockRadicalRows_spec F S₀ 0 K a ha).1,
    (sourceQuadraticBlockRadicalRows_spec F S₀ 0 K a ha).2, hnorm⟩

theorem sourceQuadraticDualSquarefreeError_exterior (b c g : E)
    (hb : sourceReflectionIsSquarefree b) (hc : sourceReflectionIsSquarefree c)
    (hg : b ⊓ c = g)
    (hclass : sourceQuadraticLocalClass F S₀ hζ b = sourceQuadraticLocalClass F S₀ hζ c)
    (X K σ : ℝ) :
    sourceQuadraticDualSquarefreeError F S₀ hζ ((b-g)+(c-g)) X K σ =
      ∑ d ∈ HeckeIdealMobius.divisors F (quadraticHeckeIdealRadical F Bad),
        ∑ a ∈ sourceQuadraticDualExteriorRows F S₀ K d,
          (Ψ ((b-g)+(c-g))).allCoefficient (I a) *
            quadraticHeckeCoprimeContourRemainder F (C ((b-g)+(c-g)))
              (quadraticHeckeSquareMellin (quadraticHeckeDualMellin A r sourceQuadraticBlockProfile))
              σ (Real.sqrt ((Ideal.absNorm (C ((b-g)+(c-g))) : ℝ) /
                (X*((q a : ℝ)*(Ideal.absNorm d : ℝ))))) := by
  unfold sourceQuadraticDualSquarefreeError
  rw [sourceQuadraticDual_all_ideal_rows F S₀ hζ b c g hb hc hg hclass K]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro d _
  unfold sourceQuadraticDualExteriorRows
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro a _
  split_ifs
  · rw [sourceQuadraticSmallPair_coefficient F S₀ hζ b c g hb hc hg a,
      map_mul, Nat.cast_mul, sourcePrimeExponentIdeal_norm]
  · rfl

end
end ArtinMatthews.SourceEulerAssembly
