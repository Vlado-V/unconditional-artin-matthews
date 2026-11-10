module

public import ArtinMatthews.StandardAdelicLocalNontrivial
public import Mathlib.Algebra.AffineMonoid.Basic


set_option backward.privateInPublic true
@[expose] public section

/-! The exceptional local conductor set is exactly the prime support of
the actual different ideal. -/
namespace ArtinMatthews.StandardAdelic

open NumberField IsDedekindDomain FractionalIdeal
open scoped NumberField nonZeroDivisors Classical
noncomputable section
variable (K : Type) [Field K] [NumberField K]

theorem count_coe_ne_zero_iff_dvd (P : HeightOneSpectrum (𝓞 K)) (I : Ideal (𝓞 K)) (hI : I ≠ ⊥) :
    FractionalIdeal.count K P I ≠ 0 ↔ P.asIdeal ∣ I := by
  rw [FractionalIdeal.count_coe K P hI, Int.natCast_ne_zero]
  exact Associates.count_ne_zero_iff_dvd hI P.irreducible

theorem mem_traceBadPlaces_iff_different (P : HeightOneSpectrum (𝓞 K)) :
    P ∈ traceBadPlaces K ↔ P.asIdeal ∣ differentIdeal ℤ (𝓞 K) := by
  have hc : FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 K)⁰ K) =
      ((differentIdeal ℤ (𝓞 K) : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K)⁻¹ := by
    rw [coeIdeal_differentIdeal ℤ ℚ K (𝓞 K), inv_inv]
  rw [mem_traceBadPlaces, hc, FractionalIdeal.count_inv, neg_ne_zero]
  exact count_coe_ne_zero_iff_dvd K P _ differentIdeal_ne_bot

end
end ArtinMatthews.StandardAdelic
