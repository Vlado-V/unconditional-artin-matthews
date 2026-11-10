module

public import ArtinMatthews.SourcePrincipalBallFrequency
public import ArtinMatthews.SourcePrincipalBallPeriodicPoisson
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

/-! Transfer the finite dual weight to the literal principal modulus and
write the Fourier argument as the original source frequency divided by
its generator. -/
namespace ArtinMatthews.SourcePhysical

open NumberField NumberField.InfinitePlace IsDedekindDomain FractionalIdeal
open VaryingKummerAnalytic SIntegerPrincipalization StandardAdelic
open scoped NumberField Classical nonZeroDivisors SchwartzMap
noncomputable section
variable (K : Type) [Field K] [NumberField K]
variable (S₀ : Finset (HeightOneSpectrum (𝓞 K)))

local notation "FI" => FractionalIdeal (𝓞 K)⁰ K
local notation "S" => principalizingSet S₀
local notation "OS" => PrincipalIntegerRing S₀
local notation "d" => principalizingDenominator S₀
local notation "CPlaces" => {v : InfinitePlace K // IsComplex v}

def sourcePrincipalQuotientFourier (a : OS) (ha : a ≠ 0)
    (w : (OS ⧸ Ideal.span {a}) → ℂ) (h : OS) : ℂ :=
  ∑' q : OS ⧸ Ideal.span {a}, w q *
    sIntegerQuotientPhase K S a ha (Ideal.Quotient.mk _ h * q)

theorem sourcePrincipalBallCoset_phase_transport (e : S → ℤ) (M : Ideal (𝓞 K))
    (hc : IsCoprime M (Ideal.span {d})) (a : OS) (ha : a ≠ 0)
    (hgen : M.map (algebraMap (𝓞 K) OS) = Ideal.span {a})
    (h : OS) (q : sourcePrincipalBallModulusQuotient K S₀ M) :
    sCharacter K S (((h : K) / (a : K)) * (sourcePrincipalBallCosetRepresentative K S₀ e M hc q : K)) =
      sIntegerQuotientPhase K S a ha
        (Ideal.Quotient.mk _ h * (Ideal.quotEquivOfEq hgen) q) := by
  let r := sourcePrincipalBallCosetRepresentative K S₀ e M hc q
  let x := sourcePrincipalBallIdealToInteger K S₀ e r
  let E := Ideal.quotEquivOfEq hgen
  have hq : Ideal.Quotient.mk (M.map (algebraMap (𝓞 K) OS)) x = q :=
    sourcePrincipalBallCosetRepresentative_spec K S₀ e M hc q
  have he : Ideal.Quotient.mk (Ideal.span {a}) x = E q :=
    (Ideal.quotEquivOfEq_mk hgen x).symm.trans (congrArg E hq)
  change sCharacter K S (((h : K) / (a : K)) * (r : K)) =
    sIntegerQuotientPhase K S a ha (Ideal.Quotient.mk _ h * E q)
  rw [← he, ← map_mul, sIntegerQuotientPhase_mk]
  change sCharacter K S (((h : K) / (a : K)) * (r : K)) =
    sCharacter K S (((h : K) * (r : K)) / (a : K))
  congr 1
  ring

theorem sourcePrincipalBallDualCoefficient_transform (e : S → ℤ) (M : Ideal (𝓞 K))
    (hc : IsCoprime M (Ideal.span {d})) (a : OS) (ha : a ≠ 0)
    (hgen : M.map (algebraMap (𝓞 K) OS) = Ideal.span {a})
    (w : (OS ⧸ Ideal.span {a}) → ℂ) (h : OS) :
    sourcePrincipalBallDualCoefficient K S₀ e M hc (fun q => w ((Ideal.quotEquivOfEq hgen) q))
        ((h : K) / (a : K)) =
      sourcePrincipalQuotientFourier K S₀ a ha w h := by
  let E := Ideal.quotEquivOfEq hgen
  unfold sourcePrincipalBallDualCoefficient sourcePrincipalQuotientFourier
  refine (tsum_congr (fun q => ?_)).trans (E.toEquiv.tsum_eq _)
  exact congrArg (fun v : ℂ => w (E q) * v)
    (sourcePrincipalBallCoset_phase_transport K S₀ e M hc a ha hgen h q)

variable [IsTotallyComplex K]

theorem sourcePrincipalBallPeriodicPoisson_frequency (e : S → ℤ) (M : Ideal (𝓞 K))
    (hM : M ≠ ⊥) (hc : IsCoprime M (Ideal.span {d})) (hS : traceBadPlaces K ⊆ S)
    (a : OS) (ha : a ≠ 0) (hgen : M.map (algebraMap (𝓞 K) OS) = Ideal.span {a})
    (hv : ∀ P : HeightOneSpectrum (𝓞 K), P ∉ S →
      P.valuation K (a : K) = WithZero.exp (-FractionalIdeal.count K P (M : FI)))
    (w : (OS ⧸ Ideal.span {a}) → ℂ) (f : CPlaces → 𝓢(ℂ, ℂ)) :
    (sourcePrincipalBallCovolume K S₀ e M hM : ℂ) *
      (∑' x : (sourceFiniteBallIdeal K S e).val,
        sourcePrincipalBallWeightedTerm K S₀ e M (fun q => w ((Ideal.quotEquivOfEq hgen) q)) f x) =
      ∑' h : SourcePrincipalBallFrequencies K S₀ e a,
        sourceNumberFieldComplexFourier K (sourceComplexTensor f)
          (sourceComplexFieldEmbedding K ((h.val : K) / (a : K))) *
          sourcePrincipalQuotientFourier K S₀ a ha w h.val := by
  let D := sourcePrincipalBallDualFrequencyEquiv K S₀ e M hM hc hS a ha hv
  refine (sourcePrincipalBallPeriodicPoisson K S₀ e M hM hc _ f).trans ?_
  refine (D.symm.tsum_eq _).symm.trans ?_
  apply tsum_congr
  intro h
  change _ * sourcePrincipalBallDualCoefficient K S₀ e M hc
    (fun q => w ((Ideal.quotEquivOfEq hgen) q)) ((h.val : K) / (a : K)) = _
  rw [sourcePrincipalBallDualCoefficient_transform K S₀ e M hc a ha hgen w]
  rfl

end
end ArtinMatthews.SourcePhysical
