module

public import ArtinMatthews.SourceKPRetainedLocalClassProfile
public import ArtinMatthews.SourceReflectionClassSelector
public import ArtinMatthews.SourceFiniteDilationIdeal
public import Mathlib.Algebra.BigOperators.Pi


set_option backward.privateInPublic true
@[expose] public section

/-! A function of the literal finite sixth-class tuple separates into
local class indicators. A continuous unitary character can be kept in
its original form and distributed across the same local factors. -/
namespace ArtinMatthews

open NumberField IsDedekindDomain ClassFieldTheory SourcePhysical SourceEulerAssembly
open scoped NumberField Classical BigOperators
noncomputable section

variable (K : Type) [Field K] [NumberField K]

section FinitePlaces
variable (S : Finset (HeightOneSpectrum (𝓞 K)))
local notation "U" => SFiniteUnits K S
local notation "Q" => SLocalPowerClasses K 6 S

def sourceKPRetainedFiniteSixthClass (z : U) : Q :=
  fun P => powerClass (P.val.adicCompletion K) 6 (z P)

def sourceKPRetainedFiniteCharacterAt (χ : U →* ℂˣ) (P : S) :
    (P.val.adicCompletion K)ˣ →* ℂˣ :=
  χ.comp (MonoidHom.mulSingle (fun P : S => (P.val.adicCompletion K)ˣ) P)

theorem sourceKPRetainedFiniteCharacterAt_continuous (χ : U →* ℂˣ)
    (hχ : Continuous χ) (P : S) : Continuous (sourceKPRetainedFiniteCharacterAt K S χ P) := by
  change Continuous (fun z : (P.val.adicCompletion K)ˣ => χ (Pi.mulSingle P z))
  exact hχ.comp (continuous_mulSingle (A := fun P : S => (P.val.adicCompletion K)ˣ) P)

theorem sourceKPRetainedFiniteCharacterAt_norm (χ : U →* ℂˣ)
    (hχ : ∀ z : U, ‖(χ z : ℂ)‖ = 1) (P : S) (z : (P.val.adicCompletion K)ˣ) :
    ‖(sourceKPRetainedFiniteCharacterAt K S χ P z : ℂ)‖ = 1 :=
  hχ (Pi.mulSingle P z)

theorem sourceKPRetainedFiniteCharacter_product (χ : U →* ℂˣ) (z : U) :
    (χ z : ℂ) = ∏ P : S, (sourceKPRetainedFiniteCharacterAt K S χ P (z P) : ℂ) := by
  have h : χ z = ∏ P : S, sourceKPRetainedFiniteCharacterAt K S χ P (z P) := by
    change χ z = ∏ P : S, χ (Pi.mulSingle P (z P))
    rw [← map_prod, Finset.univ_prod_mulSingle]
  rw [h, Units.coe_prod]
end FinitePlaces

variable {ζ : K} (hζ : IsPrimitiveRoot ζ 12) (S₀ : Finset (HeightOneSpectrum (𝓞 K)))
local notation "S" => sourceHilbertSet K S₀
local notation "U" => SFiniteUnits K S
local notation "Q" => SLocalPowerClasses K 6 S

def sourceKPRetainedFiniteSixthClassLabels : Finset Q := by
  letI : IsTotallyComplex K := source_isTotallyComplex K hζ
  exact (sourceReflectionSixthClassLabels K S₀ hζ).map
    (sWholePowerEquiv K 6 S).toEquiv.toEmbedding

@[simp] theorem mem_sourceKPRetainedFiniteSixthClassLabels (r : Q) :
    r ∈ sourceKPRetainedFiniteSixthClassLabels K hζ S₀ := by
  let : IsTotallyComplex K := source_isTotallyComplex K hζ
  unfold sourceKPRetainedFiniteSixthClassLabels
  exact Finset.mem_map.mpr ⟨(sWholePowerEquiv K 6 S).symm r,
    mem_sourceReflectionSixthClassLabels K S₀ hζ _, (sWholePowerEquiv K 6 S).apply_symm_apply r⟩

theorem sourceKPRetainedFiniteClassTensor (F : Q → ℂ) (χ : U →* ℂˣ)
    (V : ∀ P : S, (P.val.adicCompletion K)ˣ → ℂ) (z : U) :
    F (sourceKPRetainedFiniteSixthClass K S z) * (χ z : ℂ) * (∏ P : S, V P (z P)) =
      ∑ r ∈ sourceKPRetainedFiniteSixthClassLabels K hζ S₀, F r *
        ∏ P : S, sourceKPRetainedLocalClassProfile K P.val
          (sourceKPRetainedFiniteCharacterAt K S χ P) (r P) (V P) (z P) := by
  let q := sourceKPRetainedFiniteSixthClass K S z
  rw [Finset.sum_eq_single_of_mem q (mem_sourceKPRetainedFiniteSixthClassLabels K hζ S₀ q)]
  · have hδ (P : S) : sourceKPRetainedLocalClassIndicator K P.val (q P) (z P) = 1 :=
      (sourceKPRetainedLocalClassIndicator_apply K P.val (q P) (z P)).trans (ite_eq_left rfl)
    simp only [sourceKPRetainedLocalClassProfile, hδ, mul_one, Finset.prod_mul_distrib]
    rw [sourceKPRetainedFiniteCharacter_product K S χ z, mul_assoc]
  · intro r _ hr
    obtain ⟨P, hP⟩ := not_forall.mp (fun h : ∀ P : S, r P = q P => hr (funext h))
    change r P ≠ powerClass (P.val.adicCompletion K) 6 (z P) at hP
    have hlocal : sourceKPRetainedLocalClassProfile K P.val
        (sourceKPRetainedFiniteCharacterAt K S χ P) (r P) (V P) (z P) = 0 := by
      simp [sourceKPRetainedLocalClassProfile, sourceKPRetainedLocalClassIndicator_apply, Ne.symm hP]
    rw [Finset.prod_eq_zero (Finset.mem_univ P) hlocal, mul_zero]

end
end ArtinMatthews
