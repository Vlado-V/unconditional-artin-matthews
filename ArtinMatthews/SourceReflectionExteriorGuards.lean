module

public import ArtinMatthews.SourceReflectionExteriorProduct
public import ArtinMatthews.SourceReflectionExteriorBounds
public import ArtinMatthews.SourceReflectionNumeratorSeries


set_option backward.privateInPublic true
@[expose] public section

/-! Extend the exact exterior factorization to the full numerator index
by putting each support condition in its own factor. -/

namespace ArtinMatthews.SourceEulerAssembly

open NumberField IsDedekindDomain AllowedGenerators VaryingKummerAnalytic StandardAdelic QuadraticWeil SourcePhysical
open scoped NumberField Classical
noncomputable section

variable (K : Type) [Field K] [NumberField K] (S₀ : Finset (HeightOneSpectrum (𝓞 K)))
  {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
  (hS : standardWeilBadPlaces K ⊆ sourceHilbertSet K S₀)

local notation "S" => sourceHilbertSet K S₀
local notation "Pr" => SourceExteriorPrime K S₀
local notation "E" => SourcePrimeExponents K S₀
local notation "U" => exteriorUnitSubgroup S
local notation "q" => sourcePrimeExponentNorm K S₀
local notation "a₀" => sourcePrimeExponentUnit K hζ S₀
local notation "Frozen" => sourceReflectionExteriorFrozen K S₀ hζ hS
local notation "Row" => sourceReflectionExteriorRow K S₀ hζ hS
local notation "Column" => sourceReflectionExteriorColumn K S₀ hζ
local notation "Sep" => sourceReflectionExteriorSeparated K S₀ hζ hS

def sourceReflectionExteriorGuardedFrozen (ε : U) (h : E) (f : Finset Pr) (a n : E) : ℂ :=
  if ∀ P ∈ f, a P % 3 ≤ 1 ∧ n P = 0 then Frozen ε h f a n else 0

def sourceReflectionExteriorGuardedRow (ε : U) (h : E) (f : Finset Pr) (a n d : E) : ℂ :=
  if ∀ P ∈ d.support, a P = 0 ∧ n P = 0 then Row ε h f a n d else 0

local notation "GF" => sourceReflectionExteriorGuardedFrozen K S₀ hζ hS
local notation "GR" => sourceReflectionExteriorGuardedRow K S₀ hζ hS

theorem sourceReflectionExteriorGuardedFrozen_norm_le (ε : U) (h : E) (f : Finset Pr)
    (a n : E) :
    ‖GF ε h f a n‖ ≤ sourceReflectionFrozenWeight K S₀ f a := by
  unfold sourceReflectionExteriorGuardedFrozen
  split_ifs
  · exact sourceReflectionExteriorFrozen_norm_le K S₀ hζ hS ε h f a n
  · rw [norm_zero]
    exact sourceReflectionFrozenWeight_nonneg K S₀ f a

theorem sourceReflectionExteriorGuardedRow_norm_le_one (ε : U) (h : E) (f : Finset Pr)
    (a n d : E) : ‖GR ε h f a n d‖ ≤ 1 := by
  unfold sourceReflectionExteriorGuardedRow
  split_ifs
  · exact sourceReflectionExteriorRow_norm_le_one K S₀ hζ hS ε h f a n d
  · simp

theorem sourceReflectionExteriorGuardedFrozen_eq_of_supported (ε : U) (h d : E)
    (f : Finset Pr) (i : SourceReflectionTermIndex K S₀ f)
    (hi : sourceReflectionTermSupported K S₀ f d i) :
    GF ε h f i.1.val i.2.1 = Frozen ε h f i.1.val i.2.1 := by
  apply ite_eq_left
  intro P hP
  exact ⟨(hi.1 P hP).1, (hi.1 P hP).2.1⟩

theorem sourceReflectionExteriorGuardedRow_eq_of_supported (ε : U) (h d : E)
    (f : Finset Pr) (i : SourceReflectionTermIndex K S₀ f)
    (hi : sourceReflectionTermSupported K S₀ f d i) :
    GR ε h f i.1.val i.2.1 d = Row ε h f i.1.val i.2.1 d := by
  apply ite_eq_left
  intro P hP
  exact ⟨(hi.2 P hP).1, (hi.2 P hP).2.1⟩

theorem sourceReflectionExteriorGuardedFrozen_zero_of_bad_prime (ε : U) (h : E)
    (f : Finset Pr) (a n : E) {P : Pr} (hP : P ∈ f)
    (hbad : 1 < a P % 3 ∨ n P ≠ 0) : GF ε h f a n = 0 := by
  apply ite_eq_right
  intro hall
  exact hbad.elim (not_lt_of_ge (hall P hP).1) (fun hn => hn (hall P hP).2)

theorem sourceReflectionExteriorGuardedRow_zero_of_bad_prime (ε : U) (h : E)
    (f : Finset Pr) (a n d : E) {P : Pr} (hP : P ∈ d.support)
    (hbad : a P ≠ 0 ∨ n P ≠ 0) : GR ε h f a n d = 0 := by
  apply ite_eq_right
  intro hall
  exact hbad.elim (fun ha => ha (hall P hP).1) (fun hn => hn (hall P hP).2)

theorem sourceReflectionExteriorColumn_zero_of_frozen_prime (ε : U) (h : E)
    (f : Finset Pr) (a c : E) {P : Pr} (hP : P ∈ f) (hc : c P ≠ 0) :
    Column ε h f a c = 0 := by
  apply sourceReflectionExteriorColumn_eq_zero_of_not_support K S₀ hζ
  intro hs
  exact Finset.disjoint_left.mp hs.2 (Finsupp.mem_support_iff.mpr hc) hP

def sourceReflectionExteriorGuardedSeparated (ε : U) (h : E) (f : Finset Pr) (a n d c : E) : ℂ :=
  GF ε h f a n * GR ε h f a n d * Column ε h f a c * sourceReflectionQuadraticSymbol K S₀ hζ d c /
    ((Real.sqrt (q c : ℝ) : ℂ) * (q n : ℂ))

local notation "GS" => sourceReflectionExteriorGuardedSeparated K S₀ hζ hS

theorem sourceReflectionExteriorGuardedSeparated_zero_of_unsupported (ε : U) (h d : E)
    (f : Finset Pr) (i : SourceReflectionTermIndex K S₀ f)
    (hbad : ¬ sourceReflectionTermSupported K S₀ f d i) :
    GS ε h f i.1.val i.2.1 d i.2.2.val = 0 := by
  by_contra hn
  apply hbad
  have hf : ∀ P ∈ f, i.1.val P % 3 ≤ 1 ∧ i.2.1 P = 0 := by
    by_contra hG
    have hz : GF ε h f i.1.val i.2.1 = 0 := ite_eq_right hG
    exact hn (by simp only [sourceReflectionExteriorGuardedSeparated, hz, zero_mul, zero_div])
  have hr : ∀ P ∈ d.support, i.1.val P = 0 ∧ i.2.1 P = 0 := by
    by_contra hG
    have hz : GR ε h f i.1.val i.2.1 d = 0 := ite_eq_right hG
    exact hn (by simp only [sourceReflectionExteriorGuardedSeparated, hz, mul_zero, zero_mul, zero_div])
  have hc : Disjoint i.2.2.val.support f := by
    by_contra hG
    have hz := sourceReflectionExteriorColumn_eq_zero_of_not_support K S₀ hζ ε h f
      i.1.val i.2.2.val (fun h => hG h.2)
    exact hn (by simp [sourceReflectionExteriorGuardedSeparated, hz])
  have hd : Disjoint d.support i.2.2.val.support := by
    by_contra hG
    have hz := sourceReflectionQuadraticSymbol_eq_zero_of_not_disjoint K S₀ hζ d i.2.2.val hG
    exact hn (by simp [sourceReflectionExteriorGuardedSeparated, hz])
  refine ⟨fun P hP => ⟨(hf P hP).1, (hf P hP).2, ?_⟩,
    fun P hP => ⟨(hr P hP).1, (hr P hP).2, ?_⟩⟩
  · exact Finsupp.notMem_support_iff.mp (fun hm => Finset.disjoint_left.mp hc hm hP)
  · exact Finsupp.notMem_support_iff.mp (Finset.disjoint_left.mp hd hP)

theorem sourceReflectionExteriorGuardedSeparated_eq_if_supported (ε : U) (h d : E)
    (f : Finset Pr) (i : SourceReflectionTermIndex K S₀ f) :
    GS ε h f i.1.val i.2.1 d i.2.2.val =
      if sourceReflectionTermSupported K S₀ f d i then
        Sep ε h f i.1.val i.2.1 d i.2.2.val else 0 := by
  by_cases hi : sourceReflectionTermSupported K S₀ f d i
  · rw [ite_eq_left hi, sourceReflectionExteriorGuardedSeparated, sourceReflectionExteriorSeparated,
      sourceReflectionExteriorGuardedFrozen_eq_of_supported K S₀ hζ hS ε h d f i hi,
      sourceReflectionExteriorGuardedRow_eq_of_supported K S₀ hζ hS ε h d f i hi]
  · rw [ite_eq_right hi,
      sourceReflectionExteriorGuardedSeparated_zero_of_unsupported K S₀ hζ hS ε h d f i hi]

theorem sourceReflectionExteriorGuardedSeparated_eq_supported_frequency (h d : E) (f : Finset Pr)
    (hf : f ∈ sourceReflectionActiveChoices K S₀ h) (hd : sourceReflectionIsSquarefree d)
    (hdh : Disjoint d.support h.support)
    (i : SourceReflectionSupportedTermIndex K S₀ f d)
    (u : ExteriorUnitSixthClasses S) (γ : sNormOneSixthSubgroup K S) :
    GS (sourceExteriorUnitSixthRepresentative S u) h f i.val.1.val i.val.2.1 d i.val.2.2.val =
      sourceReflectionSignedExteriorProduct K S₀ hζ hS (h + d) (f ∪ d.support)
        (sourceReflectionSupportedFrequencyEquiv K S₀ hζ
          (a₀ (sourceReflectionActiveExponents K S₀ f + d)) f d (i,u,γ)).val.val := by
  rw [sourceReflectionExteriorGuardedSeparated_eq_if_supported K S₀ hζ hS
    (sourceExteriorUnitSixthRepresentative S u) h d f i.val,
    ite_eq_left (show sourceReflectionTermSupported K S₀ f d i.val from i.property)]
  exact (sourceReflectionSignedExteriorProduct_supported_frequency K S₀ hζ hS
    h d f hf hd hdh i u γ).symm

end
end ArtinMatthews.SourceEulerAssembly
