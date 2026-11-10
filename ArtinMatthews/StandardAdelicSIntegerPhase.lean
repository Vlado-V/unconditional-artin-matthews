module

public import ArtinMatthews.StandardAdelicFiniteProduct
public import Mathlib.RingTheory.DedekindDomain.SInteger
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

/-! The source S-place character and its genuine quotient phases on the
actual valuation-defined S-integer ring. No PID or generator existence
hypothesis is used. -/
namespace ArtinMatthews.StandardAdelic

open NumberField IsDedekindDomain
open OAI.RepresentationTheory.Weil.AdelicSplitting
open scoped NumberField BigOperators Classical
noncomputable section
variable (K : Type) [Field K] [NumberField K]

abbrev sIntegerRing (S : Finset (HeightOneSpectrum (𝓞 K))) :=
  ↥(Set.integer (R := 𝓞 K) (↑S : Set (HeightOneSpectrum (𝓞 K))) K)

theorem sCharacter_integer (S : Finset (HeightOneSpectrum (𝓞 K))) (x : sIntegerRing K S) :
    sCharacter K S (x : K) = 1 := by
  rw [sCharacter_exterior_product]
  apply Finset.prod_eq_one
  intro P hP
  apply localFiniteCharacter_integral
  have hx : P.valuation K (x : K) ≤ 1 := x.property P (Finset.mem_sdiff.mp hP).2
  change Valued.v (-(algebraMap K (P.adicCompletion K) (x : K))) ≤ 1
  rw [Valuation.map_neg]
  change Valued.v ((x : K) : P.adicCompletion K) ≤ 1
  rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
  exact hx

def sIntegerModulusPhase (S : Finset (HeightOneSpectrum (𝓞 K)))
    (a : sIntegerRing K S) : AddChar (sIntegerRing K S) ℂ where
  toFun x := sCharacter K S ((x : K) / (a : K))
  map_zero_eq_one' := by simp
  map_add_eq_mul' x y := by
    change sCharacter K S (((x : K)+(y : K))/(a : K)) = _
    rw [add_div, AddChar.map_add_eq_mul]

theorem sIntegerModulusPhase_period (S : Finset (HeightOneSpectrum (𝓞 K)))
    (a : sIntegerRing K S) (ha : a ≠ 0) (x : sIntegerRing K S)
    (hx : x ∈ Ideal.span {a}) : sIntegerModulusPhase K S a x = 1 := by
  obtain ⟨b,hb⟩ := Ideal.mem_span_singleton.mp hx
  have haK : (a : K) ≠ 0 := by
    intro h
    apply ha
    exact Subtype.ext h
  change sCharacter K S ((x : K)/(a : K)) = 1
  rw [hb]
  change sCharacter K S (((a : K)*(b : K))/(a : K)) = 1
  rw [mul_div_cancel_left₀ _ haK]
  exact sCharacter_integer K S b

def sIntegerQuotientPhase (S : Finset (HeightOneSpectrum (𝓞 K)))
    (a : sIntegerRing K S) (ha : a ≠ 0) : AddChar ((sIntegerRing K S) ⧸ Ideal.span {a}) ℂ :=
  AddChar.toAddMonoidHomEquiv.symm (QuotientAddGroup.lift (Ideal.span {a}).toAddSubgroup
    (sIntegerModulusPhase K S a).toAddMonoidHom (fun x hx => sIntegerModulusPhase_period K S a ha x hx))

theorem sIntegerQuotientPhase_mk (S : Finset (HeightOneSpectrum (𝓞 K)))
    (a : sIntegerRing K S) (ha : a ≠ 0) (x : sIntegerRing K S) :
    sIntegerQuotientPhase K S a ha (Ideal.Quotient.mk _ x) = sCharacter K S ((x : K)/(a : K)) := rfl

theorem sIntegerQuotientPhase_exterior (S : Finset (HeightOneSpectrum (𝓞 K)))
    (a : sIntegerRing K S) (ha : a ≠ 0) (x : sIntegerRing K S) :
    sIntegerQuotientPhase K S a ha (Ideal.Quotient.mk _ x) =
      ∏ P ∈ rationalSupport K ((x : K)/(a : K)) \ S,
        localFiniteCharacter K P (-(algebraMap K (P.adicCompletion K) ((x : K)/(a : K)))) := by
  rw [sIntegerQuotientPhase_mk, sCharacter_exterior_product]

end
end ArtinMatthews.StandardAdelic
