module

public import ArtinMatthews.QuadraticKummer
public import Mathlib.NumberTheory.RamificationInertia.Valuation
public import Mathlib.NumberTheory.RamificationInertia.Unramified


set_option backward.privateInPublic true
@[expose] public section

/-! A radical of valuation one ramifies in the actual quadratic field.
The proof uses the exact restriction of the discrete ideal valuations. -/
namespace ArtinMatthews
open NumberField IsDedekindDomain
open scoped NumberField Classical
noncomputable section

variable {F : Type} [Field F] [NumberField F] [Algebra F ℂ]

theorem quadraticKummer_ramified_of_valuation_one (u : Fˣ)
    (v : HeightOneSpectrum (𝓞 F)) (w : HeightOneSpectrum (𝓞 (QuadraticKummerField u)))
    [w.asIdeal.LiesOver v.asIdeal]
    (hv : v.valuation F (u : F) = WithZero.exp (-1 : ℤ)) :
    ¬ Algebra.IsUnramifiedAt (𝓞 F) w.asIdeal := by
  intro h
  let : Algebra.IsUnramifiedAt (𝓞 F) w.asIdeal := h
  let L := QuadraticKummerField u
  have he : w.asIdeal.ramificationIdx (𝓞 F) = 1 :=
    Ideal.ramificationIdx_eq_one_of_isUnramifiedAt
  have hw := HeightOneSpectrum.valuation_liesOver L v w (u : F)
  rw [he, pow_one, hv] at hw
  have hz := congrArg (w.valuation L) (quadraticKummerRoot_sq u)
  rw [map_pow, ← hw] at hz
  have hne : w.valuation L (quadraticKummerRoot u) ≠ 0 :=
    (Valuation.ne_zero_iff _).mpr (quadraticKummerRoot_ne_zero u)
  let n := WithZero.log (w.valuation L (quadraticKummerRoot u))
  have hlog : WithZero.exp n = w.valuation L (quadraticKummerRoot u) := WithZero.exp_log hne
  rw [← hlog, ← WithZero.exp_nsmul, WithZero.exp_inj] at hz
  change 2 • n = -1 at hz
  simp only [nsmul_eq_mul, Nat.cast_ofNat] at hz
  omega

end
end ArtinMatthews
