module

public import ArtinMatthews.SLocalBilinearForm
public import ArtinMatthews.AlternatingIsotropicComplement


set_option backward.privateInPublic true
@[expose] public section

/-! Actual isotropic complements for the prime-exponent S-local Hilbert
spaces. Every arithmetic input to the finite-field complement theorem
is proved; no self-orthogonality or complement premise is supplied. -/

namespace ArtinMatthews

open NumberField IsDedekindDomain KummerTheory
open GlobalClassFieldTheory.GlobalClassFields GlobalClassFieldTheory.Reciprocity
open SIntegerPrincipalization
open scoped NumberField Classical
noncomputable section
variable (K : Type) [Field K] [NumberField K]

theorem normSupport_exponent_subset (n : ℕ+)
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (hS : sUnitKummerNormSupport (K := K) n ∅ ⊆ S) :
    powerResidueExponentFinitePlaces K n ⊆ S := by
  intro v hv
  apply hS
  apply mem_sUnitKummerNormSupport_of_asIdeal_dvd_natCast n ∅
  exact (mem_powerResidueExponentFinitePlaces_iff K n v).mp hv

variable [NumberField.IsTotallyComplex K]

theorem sLocal_exists_isotropic_complement (n : ℕ+) [Fact (n : ℕ).Prime]
    {ζ : Kˣ} (hζ : IsPrimitiveRoot ζ (n : ℕ))
    (hminus : ∃ a : Kˣ, a ^ (n : ℕ) = -1)
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (hS : sUnitKummerNormSupport (K := K) n ∅ ⊆ S) :
    ∃ B : Submodule (ZMod (n : ℕ)) (Additive (SLocalPowerClasses K n S)),
      IsCompl (sUnitPowerSubmodule K n S) B ∧
        ∀ x ∈ B, ∀ y ∈ B,
          sLocalHilbertForm K n (sLocalPrimitiveRoots K n hζ) S
            (Additive.toMul x) (Additive.toMul y) = 1 := by
  let : Finite (Additive (SLocalPowerClasses K n S)) :=
    sLocalBilinearForm_finite K n (sLocalPrimitiveRoots K n hζ) S hS
  obtain ⟨B, hB, hIso⟩ := exists_isotropic_complement_of_card
    (sLocalBilinearForm K n hζ S) (sLocalBilinearForm_isAlt K n hζ hminus S)
    (sLocalBilinearForm_nondegenerate K n hζ S) (sUnitPowerSubmodule K n S)
    (sLocalBilinearForm_unitSubmodule_isotropic K n hζ S (normSupport_exponent_subset K n S hS))
    (sLocalBilinearForm_card_relation K n (sLocalPrimitiveRoots K n hζ) S hS)
  refine ⟨B, hB, ?_⟩
  intro x hx y hy
  exact (sLocalRootLog_eq_zero_iff K n hζ _).mp (hIso x hx y hy)

end
end ArtinMatthews
