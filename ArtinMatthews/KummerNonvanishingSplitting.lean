module

public import ArtinMatthews.KummerGaussianSplitting


set_option backward.privateInPublic true
@[expose] public section

/-! The corrected-signal route can supply actual source nonvanishing
directly. This adapter preserves the principal alternative, the genuine
primitive character, and its conductor budget, without identifying a
corrected signal with a pure Gaussian signal. -/
namespace ArtinMatthews.VaryingKummerAnalytic
open NumberField
open OAI.SevenEighths.FiniteFourier
open scoped NumberField Classical
noncomputable section

theorem primeKummer_zero_region_of_source_nonvanishing
    (q : ℕ) (a : ℤ) [NeZero q] [NeZero a]
    (hprime : q.Prime) (hq : 2 < q) (haq : a.natAbs ≤ q)
    (β : ℝ) (hβ : 0 ≤ β)
    (hprincipal : ∀ s : ℂ,β < s.re →
      mixedRegularizedDedekindZeta (twelfthCyclotomicField q) s ≠ 0)
    (hprimitive : ∀ (f : Ideal (𝓞 (twelfthCyclotomicField q))) (hf : f ≠ ⊥)
      (ψ : EvenIdealRayCharacter (twelfthCyclotomicField q) f)
      (hprim : IsPrimitiveOnIdeals ψ.residue), ψ.IsNonprincipal →
      ψ.coefficient ≠ ψ.inverse.coefficient →
      Real.log (f.absNorm : ℝ) ≤ (12*q:ℝ)*((72*(q:ℝ)^2+2)*Real.log (12*q)) →
      ∀ s : ℂ,β < s.re → ψ.primitiveContinued hf hprim s ≠ 0) :
    ∀ s : ℂ,mixedCompletedDedekindXi (primeKummerField q a) s = 0 → s.re ≤ β := by
  intro s hz
  by_contra hs
  have hsr : β < s.re := lt_of_not_ge hs
  rcases primeKummer_prime_xi_zero_sources q a hprime hq haq (lt_of_le_of_lt hβ hsr) hz with
    hbase | ⟨w,hnonreal,_,hconductor⟩
  · exact hprincipal s hsr hbase
  · exact hprimitive w.conductor w.conductor_ne_zero w.primitiveCharacter w.primitive
      w.nonprincipal hnonreal hconductor s hsr w.zero

theorem exists_primeKummer_split_count_of_source_nonvanishing :
    ∃ C : ℝ,0 < C ∧ ∀ (q : ℕ) (a : ℤ) [NeZero q] [NeZero a],
      a ≠ 1 → a ≠ -1 → q.Prime → 2 < q → a.natAbs ≤ q →
      ∀ β : ℝ,0 ≤ β →
      (∀ s : ℂ,β < s.re → mixedRegularizedDedekindZeta (twelfthCyclotomicField q) s ≠ 0) →
      (∀ (f : Ideal (𝓞 (twelfthCyclotomicField q))) (hf : f ≠ ⊥)
        (ψ : EvenIdealRayCharacter (twelfthCyclotomicField q) f)
        (hprim : IsPrimitiveOnIdeals ψ.residue), ψ.IsNonprincipal →
        ψ.coefficient ≠ ψ.inverse.coefficient →
        Real.log (f.absNorm : ℝ) ≤ (12*q:ℝ)*((72*(q:ℝ)^2+2)*Real.log (12*q)) →
        ∀ s : ℂ,β < s.re → ψ.primitiveContinued hf hprim s ≠ 0) →
      ∀ (x : ℝ) (S : Finset Nat.Primes),1 < x →
        (∀ p ∈ S,x ≤ (p : ℝ) ∧ (p : ℝ) ≤ 2*x ∧
          ¬ (p.val : ℤ) ∣ (q : ℤ) ∧ (a : ZMod p.val) ≠ 0 ∧ q ∣ multiplicativeIndex p a) →
        (S.card : ℝ) ≤ C*(x/((q : ℝ)*((q : ℝ)-1)*Real.log x)+
          x^β*Real.log (2*(q : ℝ))/Real.log x) := by
  obtain ⟨C,hC,hbound⟩ := exists_primeKummer_split_count_bound_of_zero_region
  refine ⟨C,hC,?_⟩
  intro q a _ _ ha1 ham1 hprime hq haq β hβ hprincipal hprimitive x S hx hS
  exact hbound a (NeZero.ne a) ha1 ham1 q hprime haq x β S hx hβ
    (primeKummer_zero_region_of_source_nonvanishing q a hprime hq haq
      β hβ hprincipal hprimitive) hS

end
end ArtinMatthews.VaryingKummerAnalytic
