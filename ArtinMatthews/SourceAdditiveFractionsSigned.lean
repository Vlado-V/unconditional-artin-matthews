module

public import ArtinMatthews.SourceAdditiveCompactBox
public import ArtinMatthews.SourceReducedFractionTraceLift
public import ArtinMatthews.SourceAdditiveFractionsSieve
public import ArtinMatthews.SourcePrimeExponentProducts
public import ArtinMatthews.SourcePrincipalBallPoissonCoset
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

/-! The negative row orientation used by the actual probe Gauss sum.
The original fixed generators and all quotient units are retained. -/
namespace ArtinMatthews.SourcePhysical

open NumberField IsDedekindDomain AllowedGenerators StandardAdelic
open scoped NumberField Classical BigOperators
noncomputable section
variable (F : Type) [Field F] [NumberField F]
variable (S₀ : Finset (HeightOneSpectrum (𝓞 F))) {ζ : F}

local notation "S" => sourceHilbertSet F S₀
local notation "R" => sourceRing F S₀
local notation "E" => SourcePrimeExponents F S₀
local notation "q" => sourcePrimeExponentNorm F S₀

theorem sourceReducedFractionPhase_neg (a : E → R) (ha : ∀ e, a e ≠ 0)
    (p : SourceReducedFractionLabel F S₀ a) (m : R) :
    sourceReducedFractionPhase F S₀ a ha p (-m) = star (sourceReducedFractionPhase F S₀ a ha p m) := by
  let x : R := Quotient.out (p.2 : R ⧸ Ideal.span {a p.1})
  have hx : Ideal.Quotient.mk (Ideal.span {a p.1}) x = (p.2 : R ⧸ Ideal.span {a p.1}) :=
    Ideal.Quotient.mk_out _
  rw [sourceReducedFractionPhase_eq_lift F S₀ a ha p (-m) x hx,
    sourceReducedFractionPhase_eq_lift F S₀ a ha p m x hx, Subalgebra.coe_neg, neg_mul,
    AddChar.map_neg_eq_inv]
  exact Complex.inv_eq_conj (sourceSCharacter_norm F (sourceHilbertSeed F S₀) _)

variable (hζ : IsPrimitiveRoot ζ 12)
local notation "a" => sourcePrimeExponentGenerator F hζ S₀
local notation "ha" => sourcePrimeExponentGenerator_ne_zero F hζ S₀

/-- Signed source additive sieve with the very same fixed denominator
and residue phase used in the physical Gauss sum. -/
theorem sourceFixedProductSignedAdditiveSieve
    (htrace : traceBadPlaces F ⊆ S)
    (B : Set (SLocalAdditiveCompletionSpace F S)) (hB : IsCompact B) :
    ∃ C : ℝ, 0 < C ∧ ∀ N V : ℝ, 1 ≤ N → 1 ≤ V →
      ∀ (A : Finset R) (P : Finset (SourceReducedFractionLabel F S₀ a)),
        (∀ m ∈ A, m ∈ sourceScaledLatticeRows F S₀ hζ B N) →
        (∀ p ∈ P, (q p.1 : ℝ) ≤ V) →
        ∀ b : SourceReducedFractionLabel F S₀ a → ℂ,
          (∑ m ∈ A, ‖∑ p ∈ P, b p * sourceReducedFractionPhase F S₀ a ha p (-m)‖ ^ 2) ≤
            C * (N + V ^ 2) * ∑ p ∈ P, ‖b p‖ ^ 2 := by
  obtain ⟨C, hC, h⟩ := sourceSeparatedAdditiveFractions_sieve F S₀ hζ htrace B hB
  refine ⟨C, hC, fun N V hN hV A P hA hP b => ?_⟩
  have hgen (e : E) : (sourcePrimeExponentRingIdealEquiv F S₀ e).val = Ideal.span {a e} :=
    sourcePrimeExponentGenerator_ideal F hζ S₀ e
  have hs := (h a ha hgen N V hN hV A P hA hP).1 (fun p => star (b p))
  simp only [norm_star] at hs
  have he (m : R) : (∑ p ∈ P, b p * sourceReducedFractionPhase F S₀ a ha p (-m)) =
      star (∑ p ∈ P, star (b p) * sourceReducedFractionPhase F S₀ a ha p m) := by
    rw [star_sum]
    apply Finset.sum_congr rfl
    intro p _
    rw [sourceReducedFractionPhase_neg F S₀, star_mul, star_star, mul_comm]
  simp only [he, norm_star]
  exact hs

end
end ArtinMatthews.SourcePhysical
