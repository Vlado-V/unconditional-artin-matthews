module

public import ArtinMatthews.SourcePoissonOriginalProbe
public import ArtinMatthews.SourcePrimeIdealFactorization


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews.SourceEulerAssembly
open NumberField IsDedekindDomain AllowedGenerators SourcePhysical
open scoped NumberField
noncomputable section

variable (F : Type) [Field F] [NumberField F]
variable (S₀ : Finset (HeightOneSpectrum (𝓞 F)))

/-- The fixed positive compact weight leaves only finitely many exterior ideals
in the physical (s)-sum, independently of the quotient representative. -/
theorem sourcePoissonOriginalCompactWeight_finite {Y : ℝ} (hY : 0 < Y) :
    (Function.support (fun s : SourcePrimeExponents F S₀ =>
      sourceProbeW1Complex ((sourcePrimeExponentNorm F S₀ s : ℝ) / Y))).Finite := by
  let N : ℕ := ⌈(5 / 2 : ℝ) * Y⌉₊
  let f := sourcePrimeExponentIdeal F S₀
  have hf : Function.Injective f := sourcePrimeExponentIdeal_injective F S₀
  apply ((Ideal.finite_setOfPred_absNorm_le (S := 𝓞 F) N).preimage hf.injOn).subset
  intro s hs
  have hm : ((sourcePrimeExponentNorm F S₀ s : ℝ) / Y) ∈ tsupport sourceProbeW1Complex :=
    subset_tsupport _ hs
  rw [sourceProbeW1Complex_tsupport] at hm
  have hN : (sourcePrimeExponentNorm F S₀ s : ℝ) ≤ (N : ℝ) :=
    ((div_le_iff₀ hY).mp hm.2).trans (Nat.le_ceil ((5 / 2 : ℝ) * Y))
  change Ideal.absNorm (sourcePrimeExponentIdeal F S₀ s) ≤ N
  rw [sourcePrimeExponentIdeal_norm]
  exact_mod_cast hN

end
end ArtinMatthews.SourceEulerAssembly
