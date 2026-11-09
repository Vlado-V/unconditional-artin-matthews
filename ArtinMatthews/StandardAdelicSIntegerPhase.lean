module

public import ArtinMatthews.StandardAdelicFiniteProduct
public import Mathlib.RingTheory.DedekindDomain.SInteger


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
