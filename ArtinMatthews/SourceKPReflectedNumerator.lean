module

public import ArtinMatthews.SourceReflectionSupportedFrequency


set_option backward.privateInPublic true
@[expose] public section

/-! The reflected archimedean Fourier frequency is the numerator of the
signed exterior argument. Its exact norm and unit-sixth orbit are
retained when reindexing the differentiated physical series. -/
namespace ArtinMatthews
open NumberField IsDedekindDomain SourceEulerAssembly SourcePhysical
open scoped NumberField Classical BigOperators
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
    (S₀ : Finset (HeightOneSpectrum (𝓞 K)))
local notation "S" => sourceHilbertSet K S₀
local notation "E" => SourcePrimeExponents K S₀
local notation "PE" => SourceExteriorPrime K S₀
local notation "Whole" => SWholeUnits K S
local notation "Γ" => sNormOneSixthSubgroup K S
local notation "X" => ExteriorUnitSixthClasses S
local notation "D" => sWholeDiagonal K S
local notation "gen" => sourcePrimeExponentUnit K hζ S₀
local notation "b[" f "," d "]" => gen (sourceReflectionActiveExponents K S₀ f+d)
local notation "I[" f "," d "]" => SourceReflectionSupportedTermIndex K S₀ f d
local notation "N[" f "," d "]" => SourceReflectionSupportedFrequency K S₀ (b[f,d]) d
local notation "ν[" f "," d "]" => sourceReflectionSupportedFrequencyEquiv K S₀ hζ (b[f,d]) f d

def sourceKPReflectedNumerator (f : Finset PE) (d : E) (i : I[f,d]) (u : X) (γ : Γ) : Kˣ :=
  (ν[f,d] (i,u,γ)).val.val * (b[f,d]) ^ 2

def sourceKPReflectedNumeratorBase (f : Finset PE) (d : E) (i : I[f,d]) (u : X) : Whole :=
  D ((sourceExteriorUnitSixthRepresentative S u).val * gen i.val.1.val *
    gen i.val.2.2.val * (gen i.val.2.1)^3)

theorem sourceKPReflectedNumerator_diagonal (f : Finset PE) (d : E) (i : I[f,d]) (u : X) (γ : Γ) :
    D (sourceKPReflectedNumerator K hζ S₀ f d i u γ) =
      (γ.val : Whole) * sourceKPReflectedNumeratorBase K hζ S₀ f d i u := by
  unfold sourceKPReflectedNumerator sourceKPReflectedNumeratorBase
  rw [map_mul D,sourceReflectionSupportedFrequencyEquiv_diagonal K S₀ hζ (b[f,d]) f d i u γ,
    mul_assoc,← map_mul D,div_mul_cancel]

theorem sourceKPReflectedNumeratorBase_norm (f : Finset PE) (d : E) (i : I[f,d]) (u : X) :
    sLocalNorm K S (sourceKPReflectedNumeratorBase K hζ S₀ f d i u) =
      sourceReflectionTermLength K S₀ i.val.1.val i.val.2.1 i.val.2.2.val := by
  change fieldSNorm K S _ = _
  have hunit : fieldSNorm K S (sourceExteriorUnitSixthRepresentative S u).val = 1 :=
    fieldSNorm_sUnit K S (sourceExteriorUnitToActualSUnit K S
      (sourceExteriorUnitSixthRepresentative S u))
  simp only [map_mul,map_pow,hunit,one_mul,sourcePrimeExponentUnit_fieldSNorm,
    sourceReflectionTermLength]

theorem sourceKPReflectedNumerator_div (f : Finset PE) (d : E) (i : I[f,d]) (u : X) (γ : Γ) :
    sourceKPReflectedNumerator K hζ S₀ f d i u γ / (b[f,d]) ^ 2 = (ν[f,d] (i,u,γ)).val.val := by
  exact mul_div_cancel_right _ _

theorem sourceKPReflectedNumerator_hasSum (f : Finset PE) (d : E) {A : Kˣ → ℂ} {a : ℂ}
    (h : HasSum A a)
    (hzero : ∀ m : Kˣ, m / (b[f,d]) ^ 2 ∉ Set.range (fun x : N[f,d] => x.val.val) → A m = 0) :
    HasSum (fun p : I[f,d] × (X × Γ) =>
      A (sourceKPReflectedNumerator K hζ S₀ f d p.1 p.2.1 p.2.2)) a := by
  let g (p : I[f,d] × (X × Γ)) := sourceKPReflectedNumerator K hζ S₀ f d p.1 p.2.1 p.2.2
  have hg : Function.Injective g := by
    intro p q hp
    apply (ν[f,d]).injective
    apply Subtype.ext
    apply Subtype.ext
    exact mul_right_cancel hp
  refine (hg.hasSum_iff ?_).mpr h
  intro m hm
  apply hzero m
  rintro ⟨n,hn⟩
  obtain ⟨p,rfl⟩ := (ν[f,d]).surjective n
  apply hm
  refine ⟨p,?_⟩
  change (ν[f,d] p).val.val * (b[f,d]) ^ 2 = m
  change (ν[f,d] p).val.val = m / (b[f,d]) ^ 2 at hn
  rw [hn,div_mul_cancel]

end
end ArtinMatthews
