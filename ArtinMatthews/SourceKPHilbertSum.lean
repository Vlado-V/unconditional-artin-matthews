module

public import ArtinMatthews.SourceKubotaWeylSymbol
public import ArtinMatthews.SourceFiniteKPMultipliers


set_option backward.privateInPublic true
@[expose] public section

/-! The additive Steinberg identity used in the deep compact splitting.
The finite-place specialization uses the actual cubic CFT pairing. -/

namespace ArtinMatthews
open NumberField IsDedekindDomain
open scoped NumberField
noncomputable section

theorem sourceKPHilbert_sum_trivial {F A : Type*} [Field F] [CommGroup A]
    (B : Fˣ →* (Fˣ →* A))
    (hdiag : ∀ x, B x x = 1)
    (hminus : ∀ x, B x (sourceMinusOneUnit F) = 1)
    (hsteinberg : ∀ x : Fˣ, ∀ hx : 1 - (x : F) ≠ 0, B x (Units.mk0 _ hx) = 1)
    (s a b : Fˣ) (hs : (s : F) = (a : F) + (b : F)) :
    B (s/a) (s/b) = 1 := by
  have hrel : ((b/a : Fˣ) : F) = ((s/a : Fˣ) : F) - 1 := by
    simp only [Units.val_div_eq_div_val]
    rw [hs, add_div, div_self a.ne_zero, add_sub_cancel_left]
  have hsym := sourceKubotaSymbol_steinberg_sub B hminus hsteinberg (s/a) (b/a) hrel
  have he : s/b = (s/a)/(b/a) := (div_div_div_cancel_right s b a).symm
  rw [he, map_div, hdiag, hsym, div_one]

theorem sourceFiniteKPHilbert_sum (K : Type) [Field K] [NumberField K]
    {ζ : K} (hζ : IsPrimitiveRoot ζ 12) (P : HeightOneSpectrum (𝓞 K))
    (s a b : (P.adicCompletion K)ˣ)
    (hs : (s : P.adicCompletion K) = (a : P.adicCompletion K) + (b : P.adicCompletion K)) :
    sourceFiniteKPHilbert K hζ P (s/a) (s/b) = 1 :=
  sourceKPHilbert_sum_trivial (sourceFiniteKPHilbert K hζ P)
    (sourceFiniteKPHilbert_diag K hζ P) (sourceFiniteKPHilbert_minus_right K hζ P)
    (sourceFiniteKPHilbert_steinberg K hζ P) s a b hs

end
end ArtinMatthews
