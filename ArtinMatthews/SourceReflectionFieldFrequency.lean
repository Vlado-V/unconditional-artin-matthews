module

public import ArtinMatthews.SourceReflectionFrozenWeights
public import ArtinMatthews.SourceFrequencyNormOneAction


set_option backward.privateInPublic true
@[expose] public section

/-! Multiplication by the fixed denominator square gives the exact
nonzero integral numerator of every reflected field frequency. -/
namespace ArtinMatthews.SourceEulerAssembly

open NumberField IsDedekindDomain AllowedGenerators SourcePhysical
open scoped NumberField Classical
noncomputable section

variable (F : Type) [Field F] [NumberField F]
variable (S₀ : Finset (HeightOneSpectrum (𝓞 F)))
variable {ζ : F} (hζ : IsPrimitiveRoot ζ 12)

local notation "S" => sourceHilbertSet F S₀
local notation "O" => Set.integer (R := 𝓞 F) (↑S : Set (HeightOneSpectrum (𝓞 F))) F
local notation "E" => SourcePrimeExponents F S₀
local notation "P₀" => SourceExteriorPrime F S₀
local notation "X" => ExteriorUnitSixthClasses S
local notation "Γ" => SourceExteriorUnitSixthPowers S
local notation "a" => sourcePrimeExponentUnit F hζ S₀

abbrev SourceReflectionFieldFrequency (b : Fˣ) :=
  {ν : Fˣ // ((ν*b^2 : Fˣ) : F) ∈ O}

def sourceReflectionIntegralNumerator (b : Fˣ) (ν : SourceReflectionFieldFrequency F S₀ b) :
    SourceNonzeroFrequency F S₀ :=
  ⟨⟨((ν.val*b^2 : Fˣ) : F), ν.property⟩,
    fun h => (ν.val*b^2).ne_zero (congrArg (fun z : sourceRing F S₀ => (z : F)) h)⟩

@[simp] theorem sourceReflectionIntegralNumerator_fieldUnit (b : Fˣ)
    (ν : SourceReflectionFieldFrequency F S₀ b) :
    sourceNonzeroFrequencyFieldUnit F S₀ (sourceReflectionIntegralNumerator F S₀ b ν) = ν.val*b^2 := by
  apply Units.ext
  rfl

def sourceReflectionIntegralNumeratorEquiv (b : Fˣ) :
    SourceReflectionFieldFrequency F S₀ b ≃ SourceNonzeroFrequency F S₀ where
  toFun := sourceReflectionIntegralNumerator F S₀ b
  invFun n := ⟨sourceNonzeroFrequencyFieldUnit F S₀ n / b^2, by
    rw [div_mul_cancel, sourceNonzeroFrequencyFieldUnit_val]
    exact n.val.property⟩
  left_inv ν := by
    apply Subtype.ext
    change sourceNonzeroFrequencyFieldUnit F S₀ (sourceReflectionIntegralNumerator F S₀ b ν) / b^2 = ν.val
    rw [sourceReflectionIntegralNumerator_fieldUnit, mul_div_cancel_right]
  right_inv n := by
    apply Subtype.ext
    apply Subtype.ext
    change (((sourceNonzeroFrequencyFieldUnit F S₀ n / b^2)*b^2 : Fˣ) : F) = (n.val : F)
    rw [div_mul_cancel, sourceNonzeroFrequencyFieldUnit_val]

def sourceReflectionFieldFrequencyEquiv (b : Fˣ) :
    E × (X × Γ) ≃ SourceReflectionFieldFrequency F S₀ b :=
  (((Equiv.refl E).prodCongr (sourceExteriorUnitSixthEquiv S)).trans
    (sourceFrequencyMonomialEquiv F hζ S₀)).trans (sourceReflectionIntegralNumeratorEquiv F S₀ b).symm

theorem sourceReflectionFieldFrequencyEquiv_numerator (b : Fˣ) (e : E) (u : X) (γ : Γ) :
    sourceReflectionIntegralNumerator F S₀ b (sourceReflectionFieldFrequencyEquiv F S₀ hζ b (e,u,γ)) =
      sourceFrequencyMonomial F hζ S₀ e (sourceExteriorUnitSixthEquiv S (u,γ)) := by
  change (sourceReflectionIntegralNumeratorEquiv F S₀ b)
      ((sourceReflectionIntegralNumeratorEquiv F S₀ b).symm _) = _
  exact Equiv.apply_symm_apply _ _

theorem sourceReflectionFieldFrequencyEquiv_val (b : Fˣ) (e : E) (u : X) (γ : Γ) :
    (sourceReflectionFieldFrequencyEquiv F S₀ hζ b (e,u,γ)).val =
      γ.val.val*(sourceExteriorUnitSixthRepresentative S u).val*a e/b^2 := by
  change sourceNonzeroFrequencyFieldUnit F S₀
    (sourceFrequencyMonomial F hζ S₀ e (sourceExteriorUnitSixthEquiv S (u,γ)))/b^2 = _
  congr 1
  apply Units.ext
  simp only [sourceNonzeroFrequencyFieldUnit_val, sourceFrequencyMonomial_val, Subalgebra.coe_mul,
    sourceExteriorUnitToSourceRing_val, sourceExteriorUnitSixthEquiv_apply, Subgroup.coe_mul,
    Units.val_mul, sourcePrimeExponentUnit_val]
  ac_rfl

def sourceReflectionNormOneFrequencyEquiv (b : Fˣ) :
    E × (X × sNormOneSixthSubgroup F S) ≃ SourceReflectionFieldFrequency F S₀ b :=
  ((Equiv.refl E).prodCongr ((Equiv.refl X).prodCongr
    (sourceExteriorSixthNormOneEquiv F S).symm.toEquiv)).trans (sourceReflectionFieldFrequencyEquiv F S₀ hζ b)

theorem sourceReflectionNormOneFrequencyEquiv_diagonal (b : Fˣ) (e : E) (u : X)
    (γ : sNormOneSixthSubgroup F S) :
    sWholeDiagonal F S (sourceReflectionNormOneFrequencyEquiv F S₀ hζ b (e,u,γ)).val =
      γ.val.val * sWholeDiagonal F S ((sourceExteriorUnitSixthRepresentative S u).val*a e/b^2) := by
  change sWholeDiagonal F S (sourceReflectionFieldFrequencyEquiv F S₀ hζ b
    (e,u,(sourceExteriorSixthNormOneEquiv F S).symm γ)).val = _
  rw [sourceReflectionFieldFrequencyEquiv_val, mul_assoc, mul_div_assoc, map_mul,
    ← sourceExteriorSixthNormOneEquiv_val, MulEquiv.apply_symm_apply]

theorem sourceReflectionFieldUnit_mem_integer_iff (ν : Fˣ) :
    (ν : F) ∈ O ↔ ∀ P : P₀, 0 ≤ exteriorPrincipalValuation P.val ν := by
  change (∀ P : HeightOneSpectrum (𝓞 F), P ∉ S → P.valuation F (ν : F) ≤ 1) ↔ _
  have horder (P : HeightOneSpectrum (𝓞 F)) :
      P.valuation F (ν : F) ≤ 1 ↔ 0 ≤ exteriorPrincipalValuation P ν := by
    have hν : P.valuation F (ν : F) ≠ 0 := (Valuation.ne_zero_iff _).mpr ν.ne_zero
    rw [← WithZero.log_le_log hν one_ne_zero, WithZero.log_one,
      sourceExteriorPrincipalValuation_eq_neg_log]
    omega
  exact ⟨fun h P => (horder P.val).mp (h P.val P.property),
    fun h P hP => (horder P).mpr (h ⟨P,hP⟩)⟩

theorem sourceReflectionPrimeExponentUnit_order (d : E) (P : P₀) :
    exteriorPrincipalValuation P.val (a d) = (d P : ℤ) := by
  rw [sourceExteriorPrincipalValuation_eq_neg_log, sourcePrimeExponentUnit_val,
    sourcePrimeExponentGenerator_valuation, WithZero.log_exp, neg_neg]

theorem sourceReflectionFieldFrequency_mem_iff (d : E) (ν : Fˣ) :
    ((ν*(a d)^2 : Fˣ) : F) ∈ O ↔
      ∀ P : P₀, -2*(d P : ℤ) ≤ exteriorPrincipalValuation P.val ν := by
  rw [sourceReflectionFieldUnit_mem_integer_iff]
  apply forall_congr'
  intro P
  rw [exteriorPrincipalValuation_mul, exteriorPrincipalValuation_pow, sourceReflectionPrimeExponentUnit_order]
  omega

theorem sourceReflectionFieldFrequencyEquiv_order (d e : E) (u : X) (γ : Γ) (P : P₀) :
    exteriorPrincipalValuation P.val (sourceReflectionFieldFrequencyEquiv F S₀ hζ (a d) (e,u,γ)).val =
      (e P : ℤ) - 2*(d P : ℤ) := by
  rw [sourceReflectionFieldFrequencyEquiv_val, exteriorPrincipalValuation_div,
    exteriorPrincipalValuation_mul, exteriorPrincipalValuation_mul, exteriorPrincipalValuation_pow,
    γ.val.property P.val P.property, (sourceExteriorUnitSixthRepresentative S u).property P.val P.property,
    sourceReflectionPrimeExponentUnit_order, sourceReflectionPrimeExponentUnit_order]
  simp

theorem sourceReflectionFieldFrequency_active_mem_iff (f : Finset P₀) (d : E)
    (hd : sourceReflectionIsSquarefree d) (hfd : Disjoint f d.support) (ν : Fˣ) :
    ((ν*(a (sourceReflectionActiveExponents F S₀ f+d))^2 : Fˣ) : F) ∈ O ↔
      ∀ P : P₀, (if P ∈ f ∪ d.support then -2 else 0) ≤ exteriorPrincipalValuation P.val ν := by
  rw [sourceReflectionFieldFrequency_mem_iff]
  apply forall_congr'
  intro P
  have hden : (sourceReflectionActiveExponents F S₀ f+d) P = if P ∈ f ∪ d.support then 1 else 0 := by
    simp only [Finsupp.add_apply, sourceReflectionActiveExponents, Finsupp.onFinset_apply, Finset.mem_union]
    by_cases hf : P ∈ f
    · have hn : P ∉ d.support := fun hm => Finset.disjoint_left.mp hfd hf hm
      simp [hf, Finsupp.notMem_support_iff.mp hn]
    · by_cases hp : P ∈ d.support
      · have hone : d P = 1 := by
          have hpos := Finsupp.mem_support_iff.mp hp
          have hle := hd P
          omega
        simp [hf,hp,hone]
      · simp [hf,hp,Finsupp.notMem_support_iff.mp hp]
  rw [hden]
  split_ifs <;> norm_num

end
end ArtinMatthews.SourceEulerAssembly
