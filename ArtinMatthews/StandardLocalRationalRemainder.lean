module

public import ArtinMatthews.StandardAdelicCharacter
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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

/-! The actual finite approximation defining the standard character
at one completion, retaining the rational remainder and integrality
at every other place. -/
namespace ArtinMatthews.SourcePhysical

open NumberField IsDedekindDomain StandardAdelic
open OAI.RepresentationTheory.Weil.AdelicSplitting
open scoped NumberField Classical
noncomputable section
variable (K : Type) [Field K] [NumberField K]

theorem sourceLocalRationalRemainder (P : HeightOneSpectrum (𝓞 K)) (x : P.adicCompletion K) :
    ∃ q : K,
      x - algebraMap K (P.adicCompletion K) q ∈ P.adicCompletionIntegers K ∧
      (∀ Q : HeightOneSpectrum (𝓞 K), Q ≠ P → Q.valuation K q ≤ 1) ∧
      localFiniteCharacter K P x = (rationalCharacter K q)⁻¹ := by
  let a := RestrictedProduct.single (fun Q : HeightOneSpectrum (𝓞 K) => Q.adicCompletionIntegers K) P x
  let q := finiteRationalPart K a
  have hq := finiteRationalPart_spec K a
  refine ⟨q, ?_, ?_, ?_⟩
  · have h := hq P
    change a P - algebraMap K (P.adicCompletion K) q ∈ P.adicCompletionIntegers K at h
    dsimp only [a] at h
    rwa [RestrictedProduct.single_eq_same] at h
  · intro Q hQP
    have h := hq Q
    change a Q - algebraMap K (Q.adicCompletion K) q ∈ Q.adicCompletionIntegers K at h
    dsimp only [a] at h
    rw [RestrictedProduct.single_eq_of_ne _ x hQP, zero_sub] at h
    have h' := (Q.adicCompletionIntegers K).toSubring.neg_mem h
    simp only [neg_neg] at h'
    change Valued.v (q : Q.adicCompletion K) ≤ 1 at h'
    rwa [HeightOneSpectrum.valuedAdicCompletion_eq_valuation'] at h'
  · rw [localFiniteCharacter_single]
    exact finiteCharacter_eq K a q hq

end
end ArtinMatthews.SourcePhysical
