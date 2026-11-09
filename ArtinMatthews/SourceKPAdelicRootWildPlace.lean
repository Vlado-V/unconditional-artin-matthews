module

public import ArtinMatthews.SourceKPAdelicRootCenter
public import Mathlib.RingTheory.Ideal.GoingUp


set_option backward.privateInPublic true
@[expose] public section

/-! There is an actual finite place over 2, so the adelic cubic-center
obstruction needs no choice of a finite place as a hypothesis. -/

namespace ArtinMatthews
open NumberField IsDedekindDomain
open scoped NumberField AdeleRing
noncomputable section

variable (K : Type) [Field K] [NumberField K]

theorem sourceKPAdelicRoot_exists_wild_place :
    ∃ P : HeightOneSpectrum (𝓞 K), (6 : 𝓞 K) ∈ P.asIdeal := by
  let p : Ideal ℤ := Ideal.span {(2 : ℤ)}
  have hp₀ : p ≠ ⊥ := fun hp => two_ne_zero (Ideal.span_singleton_eq_bot.mp hp)
  have hp : p.IsPrime := (Ideal.span_singleton_prime two_ne_zero).mpr Int.prime_two
  let : p.IsMaximal := hp.isMaximal hp₀
  obtain ⟨q,hq,hqp⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 K) p
  let : q.LiesOver p := hqp
  have hp₂ : (2 : ℤ) ∈ p := Ideal.subset_span (Set.mem_singleton 2)
  have hq₂ : (2 : 𝓞 K) ∈ q := by simpa using (Ideal.mem_of_liesOver q p (2 : ℤ)).mp hp₂
  have hq₀ : q ≠ ⊥ := by
    intro he
    exact (two_ne_zero : (2 : 𝓞 K) ≠ 0) (by simpa only [he,Ideal.mem_bot] using hq₂)
  refine ⟨⟨q,hq.isPrime,hq₀⟩,?_⟩
  change (6 : 𝓞 K) ∈ q
  rw [show (6 : 𝓞 K) = 3*2 by norm_num]
  exact q.mul_mem_left 3 hq₂

variable {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

theorem sourceKPAdelicRootCenter_exists_of_upper_weyl
    (A : Subgroup (SourceKPAdelicProjective K hζ))
    (hN : ∀ x : 𝔸ᶠ[K], sourceKPAdelicUpperLift K hζ (0,x) ∈ A)
    (hW : sourceKPAdelicProjectiveWeyl K hζ ∈ A) :
    ∃ z : rootsOfUnity 3 K,
      (sourceKPAdelicCentralComplex K hζ z : ℂ) ≠ 1 ∧
        sourceKPAdelicProjectiveCenter K hζ z ∈ A := by
  obtain ⟨P,_⟩ := sourceKPAdelicRoot_exists_wild_place K
  exact sourceKPAdelicRootCenter_mem_of_upper_weyl K hζ P A hN hW

end
end ArtinMatthews
