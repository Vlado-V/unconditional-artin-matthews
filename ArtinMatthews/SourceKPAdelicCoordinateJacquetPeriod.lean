module

public import ArtinMatthews.SourceKPAdelicCoordinateKernel
public import ArtinMatthews.SourceKPFiniteUnipotentConstancy
public import ArtinMatthews.SourceFinitePlaceSplit
public import ArtinMatthews.StandardLocalBall


set_option backward.privateInPublic true
@[expose] public section

/-! An actual retained-place upper period, uniform in the spectral parameter,
covering-torus coordinate and the other finite adele coordinates. -/

namespace ArtinMatthews
open NumberField IsDedekindDomain Filter Topology SourcePhysical
open scoped NumberField AdeleRing Classical
noncomputable section

variable (K : Type) [Field K] [NumberField K]
    {ζ : K} (hζ : IsPrimitiveRoot ζ 12) (P : HeightOneSpectrum (𝓞 K))

local notation "L" => P.adicCompletion K
local notation "Γ₀" => WithZero (Multiplicative ℤ)
local notation "ν" => sourceLocalValuation K P

theorem sourceLocalBall_subset_of_mem_nhds_zero {U : Set L} (hU : U ∈ 𝓝 (0 : L)) :
    ∃ n : ℤ, sourceLocalBall K P n ⊆ U := by
  obtain ⟨γ, hγ⟩ := Valued.mem_nhds_zero.mp hU
  let b : Γ₀ := MonoidWithZeroHom.ValueGroup₀.embedding γ.val
  have hb : b ≠ 0 := (map_ne_zero _).mpr γ.ne_zero
  refine ⟨WithZero.log b - 1, ?_⟩
  intro a ha
  apply hγ
  change (ν).restrict a < γ.val
  rw [Valuation.restrict_lt_iff_lt_embedding]
  change ν a < b
  calc
    ν a ≤ WithZero.exp (WithZero.log b - 1) := ha
    _ < WithZero.exp (WithZero.log b) := WithZero.exp_lt_exp.mpr (by omega)
    _ = b := WithZero.exp_log hb

local notation "G" => SourceKPAdelicProjective K hζ
local notation "D" => sourceKPAdelicDeepCompact K hζ
local notation "F₀" => sourceKPAdelicCompactSection K hζ
local notation "W₀" => sourceKPAdelicProjectiveWeyl K hζ
local notation "single₀" => sourceKPFiniteAdditiveSingle K P
local notation "N₀" => fun z : 𝔸ᶠ[K] => sourceKPAdelicUpperLift K hζ ((0, z) : 𝔸[K])

theorem sourceKPAdelicJacquetPlace_section_periodic_finite
    {I : Type*} [Finite I] (g : I → G) :
    ∃ n : ℤ, ∀ (i : I) (s : ℂ) (r : 𝔸ᶠ[K]) (x a : L), a ∈ sourceLocalBall K P n →
      (F₀ s).val (W₀ * N₀ (single₀ (x + a) + r) * g i) =
        (F₀ s).val (W₀ * N₀ (single₀ x + r) * g i) := by
  have hsingle : single₀ (0 : L) = 0 := by
    apply add_left_cancel (a := single₀ (0 : L))
    simpa only [add_zero] using (sourceKPFiniteAdditiveSingle_add K P 0 0).symm
  have hcont : Tendsto (single₀) (𝓝 (0 : L)) (𝓝 (0 : 𝔸ᶠ[K])) := by
    simpa only [hsingle] using (sourceKPFiniteAdditiveSingle_continuous K P).tendsto (0 : L)
  have hneighborhood : ∀ᶠ a : L in 𝓝 0, ∀ i, (g i)⁻¹ * N₀ (single₀ a) * g i ∈ D :=
    Filter.eventually_all.mpr fun i => hcont.eventually
      (sourceKPAdelicFiniteConjugate_eventually_compact K hζ (g i))
  obtain ⟨n, hn⟩ := sourceLocalBall_subset_of_mem_nhds_zero K P hneighborhood
  refine ⟨n, fun i s r x a ha => ?_⟩
  have he : single₀ (x + a) + r = (single₀ x + r) + single₀ a := by
    rw [sourceKPFiniteAdditiveSingle_add]
    abel
  rw [he]
  exact sourceKPAdelicCompactSection_finite_shift K hζ s W₀ (g i) (single₀ x + r) (single₀ a)
    (hn ha i)

theorem sourceKPAdelicCoordinateJacquetPlace_periodic_finite
    {I : Type*} [Finite I] (g : I → G) :
    ∃ n : ℤ, ∀ (i : I) (s : ℂ) (t : sourceKPAdelicCoveringTorus K hζ)
      (r : 𝔸ᶠ[K]) (x a : L), a ∈ sourceLocalBall K P n →
      sourceKPAdelicCoordinateKernel K hζ s (g i) t (0, single₀ (x + a) + r) =
        sourceKPAdelicCoordinateKernel K hζ s (g i) t (0, single₀ x + r) := by
  obtain ⟨n, hn⟩ := sourceKPAdelicJacquetPlace_section_periodic_finite K hζ P g
  exact ⟨n, fun i s t r x a ha => congrArg
    (fun v : SourceKPAdelicTorusInducedSpace K hζ s => v.val t) (hn i s r x a ha)⟩

theorem sourceKPAdelicCoordinateJacquetPlace_periodic (g : G) :
    ∃ n : ℤ, ∀ (s : ℂ) (t : sourceKPAdelicCoveringTorus K hζ)
      (r : 𝔸ᶠ[K]) (x a : L), a ∈ sourceLocalBall K P n →
      sourceKPAdelicCoordinateKernel K hζ s g t (0, single₀ (x + a) + r) =
        sourceKPAdelicCoordinateKernel K hζ s g t (0, single₀ x + r) := by
  obtain ⟨n, hn⟩ := sourceKPAdelicCoordinateJacquetPlace_periodic_finite K hζ P (fun _ : Unit => g)
  exact ⟨n, hn ()⟩

end
end ArtinMatthews
