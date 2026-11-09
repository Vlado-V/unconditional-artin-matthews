module

public import ArtinMatthews.SourceKPTameCyclicUpperIntegral
public import ArtinMatthews.SourceKPTameCyclicJacquetLine


set_option backward.privateInPublic true
@[expose] public section

/-! Whittaker uniqueness on the actual tame spherical cyclic
representation. Every equivariant functional is invariant under a
finite upper-root average. The Bruhat formulas make that average
zero on the kernel of the actual stable Jacquet map. -/

namespace ArtinMatthews
open NumberField IsDedekindDomain StandardAdelic SourcePhysical QuadraticWeil MeasureTheory Filter
open scoped NumberField SourcePhysical Classical
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
    (S₀ : Finset (HeightOneSpectrum (𝓞 K))) (P : SourceExteriorPrime K S₀)
    (hS : standardWeilBadPlaces K ⊆ sourceHilbertSet K S₀)

local notation "L" => P.val.adicCompletion K
local notation "C₀" => sourceKPTameSphericalCyclicSpace K hζ S₀ P
local notation "r₀" => sourceKPTameSphericalCyclicRepresentation K hζ S₀ P
local notation "f₀" => sourceKPTameCyclicSphericalVector K hζ S₀ P
local notation "l₀" => sourceFiniteKP2ProjectiveLift K hζ P.val
local notation "n₀" => fun t : L => l₀ (sourceGL2Upper t)
local notation "w₀" => l₀ sourceGL2Weyl
local notation "ψ₀" => localFiniteCharacter K P.val
local notation "B" => sourceLocalBall K P.val
local notation "μ₀" => sourceJacquetHaar K P.val
local notation "J" => sourceKPTameCyclicJacquetMap K hζ S₀ P hS
local notation "λ₀" => sourceKPTameCyclicWhittaker K hζ S₀ P hS

theorem sourceKPTameCyclicUpperAverage_eventually_zero_of_jacquet_zero (f : C₀) (hf : J f = 0) :
    ∃ M R₀ : ℕ, ∀ R ≥ R₀, sourceKPTameCyclicUpperAverage K hζ S₀ P R M f = 0 := by
  have hP : P.val ∉ traceBadPlaces K := fun h => P.property (hS (Finset.mem_union_left _ h))
  obtain ⟨M, hM⟩ := sourceKPTameCyclic_upper_small_fixed K hζ S₀ P f
  obtain ⟨T, hT⟩ := sourceKPTameCyclic_cusp_eventually_constant K hζ S₀ P f
  have hSt := sourceKPTameCyclicJacquetMap_hasStableValue K hζ S₀ P hS f
  unfold sourceKPTameJacquetHasStableValue at hSt
  obtain ⟨N, hN⟩ := eventually_atTop.mp hSt
  refine ⟨M, max 1 (max T N), fun R hR => ?_⟩
  have hR₁ : 1 ≤ R := (le_max_left _ _).trans hR
  have hRT : T ≤ R := (le_max_left T N).trans ((le_max_right _ _).trans hR)
  have hRN : N ≤ R := (le_max_right T N).trans ((le_max_right _ _).trans hR)
  have hSt₀ := hN R hRN
  have hTr : sourceKPTameJacquetInducedTruncation K hζ S₀ P f.val R = 0 := hSt₀.2.trans hf
  have hvol : 0 < Measure.real μ₀ (B (R : ℤ)) := by
    rw [sourceJacquetHaar_eq_selfDual K P.val hP]
    exact sourceLocalBall_volume_pos K P.val (R : ℤ)
  have hvol₀ : (Measure.real μ₀ (B (R : ℤ)) : ℂ) ≠ 0 := by
    exact_mod_cast hvol.ne'
  apply Subtype.ext
  apply Subtype.ext
  funext g
  have hI : (∫ t in B (R : ℤ), sourceKPTameCyclicUpperIntegrand K hζ S₀ P f g t ∂μ₀) = 0 := by
    rcases sourceFiniteKP2Projective_bruhat_cells K hζ P.val g with ⟨b, rfl⟩ | ⟨b, x, rfl⟩
    · exact sourceKPTameCyclicUpperIntegral_closed K hζ S₀ P f b hP R hR₁
    by_cases hx : x ∈ B (R : ℤ)
    · rw [sourceKPTameCyclicUpperIntegral_open_inside K hζ S₀ P f b x R hx hSt₀.1, hTr,
        smul_zero, map_zero]
    · exact sourceKPTameCyclicUpperIntegral_open_outside K hζ S₀ P f b x hP R hR₁ (fun t ht => hT R hRT x t hx ht)
  have he := (sourceKPTameCyclicUpperAverage_eval_integral K hζ S₀ P R M f g hM).trans hI
  exact (smul_eq_zero.mp he).resolve_left hvol₀

theorem sourceKPTameCyclicWhittakerFunctional_eq_zero_of_jacquet_zero
    (ℓ : C₀ →ₗ[ℂ] ℂ) (hℓ : ∀ (t : L) (f : C₀), ℓ (r₀ (n₀ t) f) = ψ₀ t * ℓ f)
    (f : C₀) (hf : J f = 0) : ℓ f = 0 := by
  obtain ⟨M, R, hR⟩ := sourceKPTameCyclicUpperAverage_eventually_zero_of_jacquet_zero K hζ S₀ P hS f hf
  have h := sourceKPTameCyclicUpperAverage_whittaker K hζ S₀ P R M f ℓ hℓ
  rw [hR R le_rfl, map_zero] at h
  exact h.symm

theorem sourceKPTameCyclicWhittakerFunctional_eq_smul
    (ℓ : C₀ →ₗ[ℂ] ℂ) (hℓ : ∀ (t : L) (f : C₀), ℓ (r₀ (n₀ t) f) = ψ₀ t * ℓ f) :
    ℓ = ℓ f₀ • λ₀ := by
  apply LinearMap.ext
  intro f
  let v := f - λ₀ f • f₀
  have hv : J v = 0 := by
    calc
      J v = J f - J (λ₀ f • f₀) := map_sub J f _
      _ = 0 := by
        rw [map_smul, sourceKPTameCyclicJacquetMap_eq_whittaker_smul K hζ S₀ P hS f, sub_self]
  have hz := sourceKPTameCyclicWhittakerFunctional_eq_zero_of_jacquet_zero K hζ S₀ P hS ℓ hℓ v hv
  have he : ℓ v = ℓ f - λ₀ f * ℓ f₀ := by
    calc
      ℓ v = ℓ f - ℓ (λ₀ f • f₀) := map_sub ℓ f _
      _ = _ := by rw [map_smul]; rfl
  have h := sub_eq_zero.mp (he.symm.trans hz)
  change ℓ f = ℓ f₀ * λ₀ f
  exact h.trans (mul_comm _ _)

theorem sourceKPTameCyclicWhittakerFunctional_unique_normalized
    (ℓ : C₀ →ₗ[ℂ] ℂ) (hℓ : ∀ (t : L) (f : C₀), ℓ (r₀ (n₀ t) f) = ψ₀ t * ℓ f)
    (hℓ₀ : ℓ f₀ = 1) : ℓ = λ₀ := by
  rw [sourceKPTameCyclicWhittakerFunctional_eq_smul K hζ S₀ P hS ℓ hℓ, hℓ₀, one_smul]

end
end ArtinMatthews
