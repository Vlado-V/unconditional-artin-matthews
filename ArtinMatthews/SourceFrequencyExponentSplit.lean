module

public import ArtinMatthews.SourcePrimeExponents


set_option backward.privateInPublic true
@[expose] public section

/-! Euclidean sixth-power splitting of the literal finite exterior
exponent vector. -/
namespace ArtinMatthews

open NumberField IsDedekindDomain
open scoped NumberField Classical
noncomputable section
variable (F : Type) [Field F] [NumberField F]
variable (S₀ : Finset (HeightOneSpectrum (𝓞 F)))

def SourceReducedFrequencyExponents :=
  {e : SourcePrimeExponents F S₀ // ∀ P : SourceExteriorPrime F S₀, e P < 6}

def sourceFrequencyExponentRemainder (e : SourcePrimeExponents F S₀) :
    SourceReducedFrequencyExponents F S₀ :=
  ⟨e.mapRange (· % 6) (by decide), fun P => Nat.mod_lt _ (by decide)⟩

def sourceFrequencyExponentQuotient (e : SourcePrimeExponents F S₀) : SourcePrimeExponents F S₀ :=
  e.mapRange (· / 6) (by decide)

@[simp] theorem sourceFrequencyExponentRemainder_apply (e : SourcePrimeExponents F S₀)
    (P : SourceExteriorPrime F S₀) :
    (sourceFrequencyExponentRemainder F S₀ e).val P = e P % 6 := rfl

@[simp] theorem sourceFrequencyExponentQuotient_apply (e : SourcePrimeExponents F S₀)
    (P : SourceExteriorPrime F S₀) :
    sourceFrequencyExponentQuotient F S₀ e P = e P / 6 := rfl

theorem sourceFrequencyExponent_decompose (e : SourcePrimeExponents F S₀) :
    (sourceFrequencyExponentRemainder F S₀ e).val + 6 • sourceFrequencyExponentQuotient F S₀ e = e := by
  ext P
  simp only [Finsupp.add_apply, Finsupp.smul_apply, sourceFrequencyExponentRemainder_apply,
    sourceFrequencyExponentQuotient_apply, nsmul_eq_mul]
  omega

theorem sourceFrequencyExponent_decompose_unique (a b : SourceReducedFrequencyExponents F S₀)
    (r s : SourcePrimeExponents F S₀) (h : a.val + 6 • r = b.val + 6 • s) :
    a = b ∧ r = s := by
  have hP (P : SourceExteriorPrime F S₀) : a.val P = b.val P ∧ r P = s P := by
    have he := congrArg (fun e : SourcePrimeExponents F S₀ => e P) h
    simp only [Finsupp.add_apply, Finsupp.smul_apply, nsmul_eq_mul] at he
    have ha := a.property P
    have hb := b.property P
    omega
  constructor
  · apply Subtype.ext
    exact Finsupp.ext fun P => (hP P).1
  · exact Finsupp.ext fun P => (hP P).2

def sourceFrequencyExponentSplit :
    SourceReducedFrequencyExponents F S₀ × SourcePrimeExponents F S₀ ≃ SourcePrimeExponents F S₀ :=
  Equiv.ofBijective (fun p => p.1.val + 6 • p.2) (by
    constructor
    · rintro ⟨a, r⟩ ⟨b, s⟩ h
      exact Prod.ext (sourceFrequencyExponent_decompose_unique F S₀ a b r s h).1
        (sourceFrequencyExponent_decompose_unique F S₀ a b r s h).2
    · intro e
      exact ⟨(sourceFrequencyExponentRemainder F S₀ e, sourceFrequencyExponentQuotient F S₀ e),
        sourceFrequencyExponent_decompose F S₀ e⟩)

@[simp] theorem sourceFrequencyExponentSplit_apply (a : SourceReducedFrequencyExponents F S₀)
    (r : SourcePrimeExponents F S₀) :
    sourceFrequencyExponentSplit F S₀ (a, r) = a.val + 6 • r := rfl

end
end ArtinMatthews
