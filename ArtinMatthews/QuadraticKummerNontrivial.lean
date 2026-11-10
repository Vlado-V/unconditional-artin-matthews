module

public import ArtinMatthews.QuadraticKummer
public import Mathlib.RingTheory.DedekindDomain.AdicValuation
public import Mathlib.MeasureTheory.Integral.Bochner.Basic


set_option backward.privateInPublic true
@[expose] public section

/-! A valuation-one radicand gives a genuine degree-two extension. -/
namespace ArtinMatthews
open NumberField IsDedekindDomain
open scoped NumberField Classical
noncomputable section

variable {F : Type} [Field F] [NumberField F]

theorem quadraticKummer_not_square_of_valuation_one (u : Fˣ)
    (v : HeightOneSpectrum (𝓞 F)) (hv : v.valuation F (u : F) = WithZero.exp (-1 : ℤ)) :
    ¬ ∃ x : F, x ^ 2 = (u : F) := by
  rintro ⟨x, hx⟩
  have hx0 : x ≠ 0 := by
    intro h
    exact u.ne_zero (by simpa only [h, zero_pow (by decide : (2 : ℕ) ≠ 0)] using hx.symm)
  have hval := congrArg (v.valuation F) hx
  rw [map_pow, hv] at hval
  have hvx : v.valuation F x ≠ 0 := (Valuation.ne_zero_iff _).mpr hx0
  rw [← WithZero.exp_log hvx, ← WithZero.exp_nsmul, WithZero.exp_inj] at hval
  change 2 • WithZero.log (v.valuation F x) = -1 at hval
  simp only [nsmul_eq_mul, Nat.cast_ofNat] at hval
  omega

variable [Algebra F ℂ] {ζ : F} (hζ : IsPrimitiveRoot ζ 6)

theorem quadraticKummerCharacter_ne_one_of_valuation_one (u : Fˣ)
    (v : HeightOneSpectrum (𝓞 F)) (hv : v.valuation F (u : F) = WithZero.exp (-1 : ℤ)) :
    quadraticKummerCharacter hζ u ≠ 1 := by
  rw [ne_eq, quadraticKummerCharacter_one_iff]
  exact quadraticKummer_not_square_of_valuation_one u v hv

include hζ in
theorem quadraticKummerField_finrank_eq_two_of_valuation_one (u : Fˣ)
    (v : HeightOneSpectrum (𝓞 F)) (hv : v.valuation F (u : F) = WithZero.exp (-1 : ℤ)) :
    Module.finrank F (QuadraticKummerField u) = 2 := by
  rcases (Nat.dvd_prime Nat.prime_two).mp (quadraticKummerField_finrank_dvd_two hζ u) with h | h
  · exfalso
    have hc : Nat.card (Gal(QuadraticKummerField u/F)) = 1 :=
      (IsGalois.card_aut_eq_finrank F (QuadraticKummerField u)).trans h
    let : Subsingleton (Gal(QuadraticKummerField u/F)) := (Nat.card_eq_one_iff_unique.mp hc).1
    apply quadraticKummerCharacter_ne_one_of_valuation_one hζ u v hv
    apply MonoidHom.ext
    intro σ
    rw [Subsingleton.elim σ 1, map_one]
    rfl
  · exact h

end
end ArtinMatthews
