module

public import ArtinMatthews.SourceSLocalPoissonCoordinates
public import ArtinMatthews.SourceSIntegerAnnularPoisson
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
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.ENatToNat
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
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Presheaf


set_option backward.privateInPublic true
@[expose] public section

/-! The periodic Poisson formula for the literal completion test. Both
Jacobian factors compose to the source S-norm. -/
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

theorem sourceSLocalDilationProbe_summable_norm (t : SWholeUnits K S) :
    Summable (fun x : OS => ‖sourceSLocalCompletionProbe K S
      (sLocalRingDiagonal K S (x : K) * sourceSLocalUnitAdditivePoint K S t⁻¹)‖) := by
  have hc : IsCoprime (⊤ : Ideal (𝓞 K)) (Ideal.span {d}) := by
    exact ⟨1, 0, by simp [Ideal.one_eq_top]⟩
  have hgen : (⊤ : Ideal (𝓞 K)).map (algebraMap (𝓞 K) OS) = Ideal.span {(1 : OS)} := by
    rw [Ideal.map_top, Ideal.span_singleton_one]
  have hs := sourceSIntegerAnnularPrimalTerm_summable_norm K S₀ ⊤ top_ne_bot hc 1 hgen
    (fun _ => 1) (sourceSLocalDilationSchwartz K S t) t.2
  simp_rw [sourceSLocalDilationProbe_eq_tensor K S t]
  simpa only [sourceSIntegerAnnularPrimalTerm, one_mul] using hs

omit [IsTotallyComplex K] in
theorem sourceSLocalDilationArchFourier (t : SWholeUnits K S) (y : CPlaces → ℂ) :
    sourceNumberFieldComplexFourier K (sourceComplexTensor (sourceSLocalDilationSchwartz K S t)) y =
      ((∏ w : CPlaces, ‖(sourceSLocalArchComplexUnits K S t w : ℂ)‖ ^ 2 : ℝ) : ℂ) *
        sourceNumberFieldComplexFourier K sourceComplexProductTest
          (fun w => (sourceSLocalArchComplexUnits K S t w : ℂ) * y w) := by
  have h (x : CPlaces → ℂ) : sourceComplexTensor (sourceSLocalDilationSchwartz K S t) x =
      ∏ w : CPlaces, sourceAnnularSchwartzTest (x w / (sourceSLocalArchComplexUnits K S t w : ℂ)) := by
    simp only [sourceComplexTensor, sourceSLocalDilationSchwartz, sourceComplexSchwartzDivDilate_apply]
  rw [funext h, sourceNumberFieldComplexFourier_divDilate]
  rfl

theorem sourceSLocalCompletionPeriodicPoisson (M : Ideal (𝓞 K))
    (hM : M ≠ ⊥) (hc : IsCoprime M (Ideal.span {d})) (hS : traceBadPlaces K ⊆ S)
    (a : OS) (ha : a ≠ 0) (hgen : M.map (algebraMap (𝓞 K) OS) = Ideal.span {a})
    (hv : ∀ P : HeightOneSpectrum (𝓞 K), P ∉ S →
      P.valuation K (a : K) = WithZero.exp (-FractionalIdeal.count K P (M : FI)))
    (w : OS ⧸ Ideal.span {a} → ℂ) (t : SWholeUnits K S) :
    (∑' x : OS, w (Ideal.Quotient.mk _ x) * sourceSLocalCompletionProbe K S
      (sLocalRingDiagonal K S (x : K) * sourceSLocalUnitAdditivePoint K S t⁻¹)) =
      ((sLocalNorm K S t : ℂ) / (Ideal.absNorm M : ℂ)) *
        ∑' h : OS, sourceSLocalCompletionFourier K S (sourceSLocalCompletionProbe K S)
          (sourceSLocalUnitAdditivePoint K S t * sLocalRingDiagonal K S ((h : K) / (a : K))) *
          sourcePrincipalQuotientFourier K S₀ a ha w h := by
  let f := sourceSLocalDilationSchwartz K S t
  let A : ℝ := ∏ w : CPlaces, ‖(sourceSLocalArchComplexUnits K S t w : ℂ)‖ ^ 2
  have hL (x : OS) : w (Ideal.Quotient.mk _ x) * sourceSLocalCompletionProbe K S
      (sLocalRingDiagonal K S (x : K) * sourceSLocalUnitAdditivePoint K S t⁻¹) =
        sourceSIntegerAnnularPrimalTerm K S₀ a w f t.2 x := by
    rw [sourceSLocalDilationProbe_eq_tensor K S t, sourceSIntegerAnnularPrimalTerm, mul_assoc]
  have hR (h : OS) : sourceSIntegerAnnularDualTerm K S₀ a ha w f t.2 h =
      (A : ℂ) * (sourceSLocalCompletionFourier K S (sourceSLocalCompletionProbe K S)
        (sourceSLocalUnitAdditivePoint K S t * sLocalRingDiagonal K S ((h : K) / (a : K))) *
        sourcePrincipalQuotientFourier K S₀ a ha w h) := by
    unfold sourceSIntegerAnnularDualTerm
    rw [show f = sourceSLocalDilationSchwartz K S t from rfl, sourceSLocalDilationArchFourier,
      sourceSLocalDilationDual_eq_tensor]
    dsimp only [A]
    ac_rfl
  have hAB : (A : ℂ) * (sourceFiniteDilationNorm K S t.2 : ℂ) = (sLocalNorm K S t : ℂ) := by
    simpa only [Complex.ofReal_mul] using congrArg Complex.ofReal (sourceSLocalDilationJacobian K S t)
  simp_rw [hL]
  rw [sourceSIntegerAnnularPeriodicPoisson K S₀ M hM hc hS a ha hgen hv w f t.2]
  simp_rw [hR, tsum_mul_left]
  rw [← hAB]
  ring

end
end ArtinMatthews.SourcePhysical
