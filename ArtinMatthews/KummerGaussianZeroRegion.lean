module

public import ArtinMatthews.KummerPrimitiveZeroSources
public import ArtinMatthews.PrincipalDedekindSourceMellin
public import ArtinMatthews.VaryingKummerAnalyticPrimitiveGaussianMellin


set_option backward.privateInPublic true
@[expose] public section

/-! Exact analytic input for the varying-q Kummer zero region. The
Big-O constants and starting points are allowed to depend on the field
and character. Only the exponent beta is shared. No power bound is
proved or assumed implicitly by a definition. -/
namespace ArtinMatthews.VaryingKummerAnalytic
open NumberField Filter Asymptotics
open OAI.SevenEighths.FiniteFourier
open scoped NumberField Classical Topology
noncomputable section

theorem primeKummer_zero_region_of_gaussian_power_bounds
    (q : ℕ) (a : ℤ) [NeZero q] [NeZero a]
    (hprime : q.Prime) (hq : 2 < q) (haq : a.natAbs ≤ q)
    (β c : ℝ) (hβ : 0 ≤ β) (hβ2 : β < 2)
    (hprincipal : principalSourceGaussianSignal (twelfthCyclotomicField q) c =O[atTop]
      (fun Z : ℝ => Z^(β+c)))
    (hprimitive : ∀ (f : Ideal (𝓞 (twelfthCyclotomicField q))) (hf : f ≠ ⊥)
      (ψ : EvenIdealRayCharacter (twelfthCyclotomicField q) f)
      (hprim : IsPrimitiveOnIdeals ψ.residue), ψ.IsNonprincipal →
      ψ.coefficient ≠ ψ.inverse.coefficient →
      Real.log (f.absNorm : ℝ) ≤ (12*q:ℝ)*((72*(q:ℝ)^2+2)*Real.log (12*q)) →
      ψ.primitiveGaussianSignal hf hprim c =O[atTop] (fun Z : ℝ => Z^(β+c))) :
    ∀ s : ℂ,mixedCompletedDedekindXi (primeKummerField q a) s = 0 → s.re ≤ β := by
  intro s hz
  by_contra hs
  have hsr : β < s.re := lt_of_not_ge hs
  have hspos : 0 < s.re := lt_of_le_of_lt hβ hsr
  rcases primeKummer_prime_xi_zero_sources q a hprime hq haq hspos hz with
    hbase | ⟨w,hnonreal,_,hconductor⟩
  · have hn := principalDedekindRegularized_ne_zero_of_sourceGaussianSignal_power_bound
      (twelfthCyclotomicField q) c β hβ2 hprincipal hsr
    apply hn
    change mixedDedekindEntireNumerator (twelfthCyclotomicField q) s = 0
    rw [mixedDedekindEntireNumerator_eq_regularized _ (by
      intro he
      simp only [he,Complex.zero_re,lt_self_iff_false] at hspos)]
    exact hbase
  · exact (w.primitiveCharacter.primitiveContinued_ne_zero_of_gaussianSignal_power_bound
      w.conductor_ne_zero w.primitive w.nonprincipal c β hβ2
      (hprimitive w.conductor w.conductor_ne_zero w.primitiveCharacter w.primitive
        w.nonprincipal hnonreal hconductor) hsr) w.zero

end
end ArtinMatthews.VaryingKummerAnalytic
