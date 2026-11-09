module

public import ArtinMatthews.SourcePrincipalAbsent


set_option backward.privateInPublic true
@[expose] public section

/-! Equality transport for a principal modulus, retaining its actual
standard phase and transporting the residue weight canonically. -/
namespace ArtinMatthews.SourceCRTNormalization

open NumberField IsDedekindDomain ArtinMatthews.SIntegerPrincipalization
open scoped NumberField Classical
noncomputable section
variable {K : Type} [Field K] [NumberField K]
variable (S₀ : Finset (HeightOneSpectrum (𝓞 K)))

theorem principalSourceKernel_congr_left (A A' B : PrincipalIntegerRing S₀) (h : A = A')
    (hA : A ≠ 0) (hA' : A' ≠ 0) (hB : B ≠ 0) (H : PrincipalIntegerRing S₀)
    (W : ((PrincipalIntegerRing S₀) ⧸ Ideal.span {A}) → ℂ)
    (Z : ((PrincipalIntegerRing S₀) ⧸ Ideal.span {B}) → ℂ) :
    principalSourceKernel S₀ A B hA hB H W Z =
      principalSourceKernel S₀ A' B hA' hB H
        (fun d => W ((Ideal.quotEquivOfEq (congrArg (fun x : PrincipalIntegerRing S₀ => Ideal.span {x}) h)).symm d)) Z := by
  cases h
  simp only [quotientEquivOfEq_refl, RingEquiv.symm_refl, RingEquiv.refl_apply]

end
end ArtinMatthews.SourceCRTNormalization
