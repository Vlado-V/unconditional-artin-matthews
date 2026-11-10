module

public import ArtinMatthews.SourceSIntegerAnnularTerms
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
public import Mathlib.RingTheory.Henselian
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

/-! Actual periodic Poisson on the S-integer ring for the finite
annular tensor. Each summation exchange uses proved absolute
convergence of the genuine ball-lattice terms. -/
namespace ArtinMatthews.SourcePhysical

open NumberField NumberField.InfinitePlace IsDedekindDomain FractionalIdeal
open VaryingKummerAnalytic SIntegerPrincipalization StandardAdelic
open scoped NumberField Classical nonZeroDivisors BigOperators SchwartzMap
noncomputable section
variable (K : Type) [Field K] [NumberField K] [IsTotallyComplex K]
variable (S₀ : Finset (HeightOneSpectrum (𝓞 K)))

local notation "FI" => FractionalIdeal (𝓞 K)⁰ K
local notation "S" => principalizingSet S₀
local notation "OS" => PrincipalIntegerRing S₀
local notation "d" => principalizingDenominator S₀
local notation "CPlaces" => {v : InfinitePlace K // IsComplex v}

private theorem summable_norm_finite_patterns {B X : Type*} [Fintype B] (g : B → X → ℂ)
    (hg : ∀ b, Summable (fun x => ‖g b x‖)) :
    Summable (fun x => ‖∑ b, g b x‖) := by
  have h : Summable (fun x => ∑ b, ‖g b x‖) := summable_sum (fun b _ => hg b)
  exact h.of_nonneg_of_le (fun _ => norm_nonneg _) (fun x => norm_sum_le _ _)

theorem sourceSIntegerAnnularPrimalTerm_summable_norm (M : Ideal (𝓞 K))
    (hM : M ≠ ⊥) (hc : IsCoprime M (Ideal.span {d}))
    (a : OS) (hgen : M.map (algebraMap (𝓞 K) OS) = Ideal.span {a})
    (w : OS ⧸ Ideal.span {a} → ℂ) (f : CPlaces → 𝓢(ℂ, ℂ)) (t : SFiniteUnits K S) :
    Summable (fun x => ‖sourceSIntegerAnnularPrimalTerm K S₀ a w f t x‖) := by
  simp_rw [sourceSIntegerAnnularPrimalTerm_patterns]
  apply summable_norm_finite_patterns
  intro b
  simp_rw [norm_mul]
  exact (sourcePrincipalBallPrimalTerm_summable_norm K S₀ _ M hM hc a hgen w f).mul_left _

theorem sourceSIntegerAnnularDualTerm_summable_norm (M : Ideal (𝓞 K))
    (hM : M ≠ ⊥) (hc : IsCoprime M (Ideal.span {d})) (hS : traceBadPlaces K ⊆ S)
    (a : OS) (ha : a ≠ 0) (hgen : M.map (algebraMap (𝓞 K) OS) = Ideal.span {a})
    (hv : ∀ P : HeightOneSpectrum (𝓞 K), P ∉ S →
      P.valuation K (a : K) = WithZero.exp (-FractionalIdeal.count K P (M : FI)))
    (w : OS ⧸ Ideal.span {a} → ℂ) (f : CPlaces → 𝓢(ℂ, ℂ)) (t : SFiniteUnits K S) :
    Summable (fun h => ‖sourceSIntegerAnnularDualTerm K S₀ a ha w f t h‖) := by
  let c : ℂ := (sourceFiniteDilationNorm K S t : ℂ)
  have hc0 : c ≠ 0 := Complex.ofReal_ne_zero.mpr (Finset.prod_pos
    (fun v _ => norm_pos_iff.mpr (t v).ne_zero)).ne'
  let e := sourceFiniteDilationExponent K S t
  let C (b : S → Fin 2) := (∏ v : S, sourceFiniteChoiceSign (b v)) * (sourceFiniteBallVolume K S₀ (e b) : ℂ)
  let g (b : S → Fin 2) (h : OS) := C b * sourcePrincipalBallDualTerm K S₀ (e b) a ha w f h
  have hg (b : S → Fin 2) : Summable (fun h => ‖g b h‖) := by
    have h0 := sourcePrincipalBallDualTerm_summable_norm K S₀ (e b) M hM hc hS a ha hgen hv w f
    exact (h0.mul_left ‖C b‖).congr
      (fun h => (norm_mul (C b) (sourcePrincipalBallDualTerm K S₀ (e b) a ha w f h)).symm)
  refine ((summable_norm_finite_patterns g hg).mul_left ‖c⁻¹‖).congr (fun h => ?_)
  rw [← norm_mul]
  rw [show (∑ b : S → Fin 2, g b h) = c * sourceSIntegerAnnularDualTerm K S₀ a ha w f t h from
      (sourceSIntegerAnnularDualTerm_patterns K S₀ a ha w f t h).symm,
    inv_mul_cancel_left₀ hc0]

theorem sourceSIntegerAnnularPeriodicPoisson (M : Ideal (𝓞 K))
    (hM : M ≠ ⊥) (hc : IsCoprime M (Ideal.span {d})) (hS : traceBadPlaces K ⊆ S)
    (a : OS) (ha : a ≠ 0) (hgen : M.map (algebraMap (𝓞 K) OS) = Ideal.span {a})
    (hv : ∀ P : HeightOneSpectrum (𝓞 K), P ∉ S →
      P.valuation K (a : K) = WithZero.exp (-FractionalIdeal.count K P (M : FI)))
    (w : OS ⧸ Ideal.span {a} → ℂ) (f : CPlaces → 𝓢(ℂ, ℂ)) (t : SFiniteUnits K S) :
    (∑' x, sourceSIntegerAnnularPrimalTerm K S₀ a w f t x) =
      ((sourceFiniteDilationNorm K S t : ℂ) / (Ideal.absNorm M : ℂ)) *
        ∑' h, sourceSIntegerAnnularDualTerm K S₀ a ha w f t h := by
  let sign (b : S → Fin 2) := ∏ v : S, sourceFiniteChoiceSign (b v)
  let e := sourceFiniteDilationExponent K S t
  let L (b : S → Fin 2) (x : OS) := sign b * sourcePrincipalBallPrimalTerm K S₀ (e b) a w f x
  let R (b : S → Fin 2) (h : OS) :=
    (sign b * (sourceFiniteBallVolume K S₀ (e b) : ℂ)) *
      sourcePrincipalBallDualTerm K S₀ (e b) a ha w f h
  have hL (b : S → Fin 2) : Summable (L b) :=
    (sourcePrincipalBallPrimalTerm_summable_norm K S₀ (e b) M hM hc a hgen w f).of_norm.mul_left _
  have hR (b : S → Fin 2) : Summable (R b) :=
    (sourcePrincipalBallDualTerm_summable_norm K S₀ (e b) M hM hc hS a ha hgen hv w f).of_norm.mul_left _
  calc
    _ = ∑' x, ∑ b : S → Fin 2, L b x :=
      tsum_congr (sourceSIntegerAnnularPrimalTerm_patterns K S₀ a w f t)
    _ = ∑ b : S → Fin 2, ∑' x, L b x := Summable.tsum_finsetSum (fun b _ => hL b)
    _ = (Ideal.absNorm M : ℂ)⁻¹ * ∑ b : S → Fin 2, ∑' h, R b h := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro b _
      unfold L R
      rw [tsum_mul_left, tsum_mul_left, sourcePrincipalBallSupportedPoisson K S₀ (e b) M hM hc hS
        a ha hgen hv w f]
      ring
    _ = (Ideal.absNorm M : ℂ)⁻¹ * ∑' h, ∑ b : S → Fin 2, R b h := by
      rw [Summable.tsum_finsetSum (fun b _ => hR b)]
    _ = _ := by
      have h (x : OS) : (∑ b : S → Fin 2, R b x) =
          (sourceFiniteDilationNorm K S t : ℂ) * sourceSIntegerAnnularDualTerm K S₀ a ha w f t x :=
        (sourceSIntegerAnnularDualTerm_patterns K S₀ a ha w f t x).symm
      simp_rw [h, tsum_mul_left]
      ring

end
end ArtinMatthews.SourcePhysical
