module

public import ArtinMatthews.SourceFrequencyNormOneAction
public import ArtinMatthews.SourceFrequencyOrbitSeparation
public import ArtinMatthews.AllowedGeneratorPowerAdjustment


set_option backward.privateInPublic true
@[expose] public section

/-! The allowed nonzero source integers have one positive orbit for each
exterior exponent vector, indexed by the distinct sixth-power S-unit image. -/
namespace ArtinMatthews
open NumberField IsDedekindDomain AllowedGenerators SourcePhysical
open scoped NumberField Classical
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
variable (S₀ : Finset (HeightOneSpectrum (𝓞 K)))
include hζ S₀
local notation "S" => sourceHilbertSet K S₀
local notation "X" => exteriorUnitSubgroup S
local notation "D" => SourceExteriorUnitSixthPowers S
local notation "E" => SourcePrimeExponents K S₀
local notation "A" => allowedSubgroup K hζ S₀
local notation "Γ" => sNormOneSixthSubgroup K S
local notation "N" => SourceNonzeroFrequency K S₀
local notation "mUnit" => sourceNonzeroFrequencyFieldUnit K S₀
local notation "a" => sourcePrimeExponentUnit K hζ S₀

abbrev SourceKPAllowedPositiveFrequency :=
  {m : N // mUnit m ∈ A}

private theorem monomial_fieldUnit (e : E) (u : X) :
    mUnit (sourceFrequencyMonomial K hζ S₀ e u) = u.val * a e := by
  apply Units.ext
  rw [sourceNonzeroFrequencyFieldUnit_val, sourceFrequencyMonomial_val, Subalgebra.coe_mul,
    sourceExteriorUnitToSourceRing_val, Units.val_mul, sourcePrimeExponentUnit_val]

private theorem monomial_sixth_allowed (e : E) (v : D) :
    mUnit (sourceFrequencyMonomial K hζ S₀ e v.val) ∈ A := by
  obtain ⟨t, ht⟩ := sourceExteriorUnitSixthPower_exists_root S v
  rw [monomial_fieldUnit, ht, mul_comm]
  change a e * ((sourceExteriorUnitToActualSUnit K S t : SUnitGroup (K := K) S) : Kˣ)^6 ∈ A
  exact adjust_sixth_preserves_allowed K hζ S₀ _ (sourcePrimeExponentUnit_allowed K hζ S₀ e)
    (sourceExteriorUnitToActualSUnit K S t)

def sourceKPAllowedPositiveFrequencyEquiv : E × D ≃ SourceKPAllowedPositiveFrequency K hζ S₀ :=
  Equiv.ofBijective (fun p =>
    ⟨sourceFrequencyMonomial K hζ S₀ p.1 p.2.val, monomial_sixth_allowed K hζ S₀ p.1 p.2⟩) (by
    constructor
    · rintro ⟨e, u⟩ ⟨f, v⟩ h
      have he : (e, u.val) = (f, v.val) :=
        (sourceFrequencyMonomialEquiv K hζ S₀).injective (congrArg Subtype.val h)
      exact Prod.ext (congrArg (fun p : E × X => p.1) he)
        (Subtype.ext (congrArg (fun p : E × X => p.2) he))
    · intro m
      obtain ⟨⟨e,u⟩, he⟩ := (sourceFrequencyMonomialEquiv K hζ S₀).surjective m.val
      change sourceFrequencyMonomial K hζ S₀ e u = m.val at he
      have ha : u.val * a e ∈ A := by
        rw [← monomial_fieldUnit, he]
        exact m.property
      have hI : toPrincipalIdeal (sourceRing K S₀) K (u.val * a e) =
          toPrincipalIdeal (sourceRing K S₀) K (a e) := by
        rw [map_mul]
        have hu : toPrincipalIdeal (sourceRing K S₀) K u.val = 1 :=
          sUnit_principal_eq_one K S₀ (sourceExteriorUnitToActualSUnit K S u)
        rw [hu, one_mul]
      obtain ⟨t, ht⟩ := allowed_ratio_sixth K hζ S₀ _ _ ha
        (sourcePrimeExponentUnit_allowed K hζ S₀ e) hI
      have hu : u.val = (t : Kˣ)^6 := by simpa only [mul_div_cancel_right] using ht
      let r := sourceActualSUnitToExteriorUnit K S t
      let v : D := ⟨r^6, ⟨r, rfl⟩⟩
      have hv : v.val = u := Subtype.ext hu.symm
      exact ⟨(e,v), Subtype.ext ((congrArg (sourceFrequencyMonomial K hζ S₀ e) hv).trans he)⟩)

theorem sourceKPAllowedPositiveFrequencyEquiv_fieldUnit (e : E) (v : D) :
    mUnit (sourceKPAllowedPositiveFrequencyEquiv K hζ S₀ (e,v)).val = a e * v.val.val := by
  change mUnit (sourceFrequencyMonomial K hζ S₀ e v.val) = _
  rw [monomial_fieldUnit, mul_comm]

/-- Use the exact image in the norm-one group, so no root multiplicity remains. -/
def sourceKPAllowedPositiveGammaEquiv : E × Γ ≃ SourceKPAllowedPositiveFrequency K hζ S₀ :=
  ((Equiv.refl E).prodCongr (sourceExteriorSixthNormOneEquiv K S).symm.toEquiv).trans
    (sourceKPAllowedPositiveFrequencyEquiv K hζ S₀)

theorem sourceKPAllowedPositiveGammaEquiv_fieldUnit (e : E) (γ : Γ) :
    mUnit (sourceKPAllowedPositiveGammaEquiv K hζ S₀ (e,γ)).val =
      a e * ((sourceExteriorSixthNormOneEquiv K S).symm γ).val.val :=
  sourceKPAllowedPositiveFrequencyEquiv_fieldUnit K hζ S₀ e _

theorem sourceKPAllowedPositiveGammaEquiv_diagonal (e : E) (γ : Γ) :
    sWholeDiagonal K S (mUnit (sourceKPAllowedPositiveGammaEquiv K hζ S₀ (e,γ)).val) =
      sWholeDiagonal K S (a e) * γ.val.val := by
  let u := (sourceExteriorSixthNormOneEquiv K S).symm γ
  change sWholeDiagonal K S (mUnit (sourceKPAllowedPositiveFrequencyEquiv K hζ S₀ (e,u)).val) = _
  rw [sourceKPAllowedPositiveFrequencyEquiv_fieldUnit, map_mul]
  have hu := congrArg (fun g : Γ => g.val.val) ((sourceExteriorSixthNormOneEquiv K S).apply_symm_apply γ)
  rw [sourceExteriorSixthNormOneEquiv_val] at hu
  rw [hu]

theorem sourceKPAllowedPositiveGammaEquiv_exponents (e : E) (γ : Γ) :
    let m := (sourceKPAllowedPositiveGammaEquiv K hζ S₀ (e,γ)).val
    sourceElementExponents K S₀ m.val m.property = e :=
  sourceFrequencyMonomial_exponents K hζ S₀ e _

theorem sourceKPAllowedPositiveFrequency_tsum (f : N → ℂ) :
    (∑' m : N, if mUnit m ∈ A then f m else 0) =
      ∑' p : E × Γ, f (sourceKPAllowedPositiveGammaEquiv K hζ S₀ p).val := by
  change (∑' m : N, ({m : N | mUnit m ∈ A} : Set N).indicator f m) = _
  rw [← tsum_subtype]
  exact ((sourceKPAllowedPositiveGammaEquiv K hζ S₀).tsum_eq
    (fun m : SourceKPAllowedPositiveFrequency K hζ S₀ => f m.val)).symm

end
end ArtinMatthews
