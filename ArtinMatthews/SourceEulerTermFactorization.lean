module

public import ArtinMatthews.SourceEulerLocalTerm
public import ArtinMatthews.SourceGlobalEulerCoefficients
public import ArtinMatthews.SourceNormPowerProducts


set_option backward.privateInPublic true
@[expose] public section

/-! Termwise factorization of the literal global source series.
All four exponent choices are retained and may have overlapping support. -/
namespace ArtinMatthews.SourceEulerAssembly
open NumberField IsDedekindDomain AllowedGenerators VaryingKummerAnalytic QuadraticWeil SourceEuler
open scoped NumberField Classical BigOperators
noncomputable section
variable (F : Type) [Field F] [NumberField F] [IsTotallyComplex F]
variable {ζ : F} (hζ : IsPrimitiveRoot ζ 12)
variable (S₀ : Finset (HeightOneSpectrum (𝓞 F)))
variable (hS : standardWeilBadPlaces F ⊆ sourceHilbertSet F S₀)
variable {M : Ideal (𝓞 F)} (η : EvenIdealRayCharacter F M)

theorem reflectionThetaValue_prefix (e : SourcePrimeExponents F S₀)
    (T : Finset (SourceExteriorPrime F S₀)) (he : e.support ⊆ T) :
    reflectionThetaValue F hζ S₀ hS η e =
      ∏ P : T, reflectionThetaValue F hζ S₀ hS η (Finsupp.single P.val 1) ^ e P.val := by
  rw [reflectionThetaValue_prod]
  calc
    _ = ∏ P ∈ T, reflectionThetaValue F hζ S₀ hS η (Finsupp.single P 1) ^ e P := by
      apply Finset.prod_subset he
      intro P _ hP
      rw [Finsupp.notMem_support_iff.mp hP]
      exact pow_zero _
    _ = _ := (Finset.prod_coe_sort T (fun P =>
      reflectionThetaValue F hζ S₀ hS η (Finsupp.single P 1) ^ e P)).symm

omit [IsTotallyComplex F] in
theorem sourceCoordinateEquiv_supports
    (a : SourceExteriorPrime F S₀ →₀ SourceLocalChoice) :
    let b := sourceCoordinateEquiv (SourceExteriorPrime F S₀) a
    b.1.val.support ⊆ a.support ∧ b.2.1.support ⊆ a.support ∧
      b.2.2.1.support ⊆ a.support ∧ b.2.2.2.support ⊆ a.support ∧
      (b.1.val + 3 • b.2.1).support ⊆ a.support := by
  let b := sourceCoordinateEquiv (SourceExteriorPrime F S₀) a
  have h (P : SourceExteriorPrime F S₀) (hp : P ∉ a.support) :
      b.1.val P = 0 ∧ b.2.1 P = 0 ∧ b.2.2.1 P = 0 ∧ b.2.2.2 P = 0 := by
    have hP := Finsupp.notMem_support_iff.mp hp
    change (a P).1.val = 0 ∧ (a P).2.1 = 0 ∧ (a P).2.2.1 = 0 ∧ (a P).2.2.2 = 0
    rw [hP]
    exact ⟨rfl, rfl, rfl, rfl⟩
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro P hp
    by_contra hn
    exact (Finsupp.mem_support_iff.mp hp) (h P hn).1
  · intro P hp
    by_contra hn
    exact (Finsupp.mem_support_iff.mp hp) (h P hn).2.1
  · intro P hp
    by_contra hn
    exact (Finsupp.mem_support_iff.mp hp) (h P hn).2.2.1
  · intro P hp
    by_contra hn
    exact (Finsupp.mem_support_iff.mp hp) (h P hn).2.2.2
  · intro P hp
    by_contra hn
    apply (Finsupp.mem_support_iff.mp hp)
    change (b.1.val + 3 • b.2.1) P = 0
    rw [Finsupp.add_apply, Finsupp.smul_apply, (h P hn).1, (h P hn).2.1, smul_zero, add_zero]

theorem sourceGlobalEulerTerm_factor (u : sourceRing F S₀) (hu : u ≠ 0) (ξ w z : ℂ)
    (a : SourceExteriorPrime F S₀ →₀ SourceLocalChoice) :
    sourceGlobalEulerTerm F hζ S₀ hS η u ξ w z
        (sourceCoordinateEquiv (SourceExteriorPrime F S₀) a) =
      finiteChoiceWeight (sourceLocalEulerTerm F hζ S₀ hS η u hu ξ w z) a := by
  let b := sourceCoordinateEquiv (SourceExteriorPrime F S₀) a
  let A := b.1.val + 3 • b.2.1
  let T := a.support
  let f := sourceLocalEulerTerm F hζ S₀ hS η u hu ξ w z
  obtain ⟨hc, hl, hk, hr, hA⟩ := sourceCoordinateEquiv_supports F S₀ a
  let Γ := reflectionGammaTwo F hζ S₀ b.1.val
  let Θ := reflectionThetaValue F hζ S₀ hS η A
  let Φ := sourceExponentFiniteF F hζ S₀ (reflectionPrimeCharacters F hζ S₀)
    b.2.2.1 A (u * sourcePrimeExponentGenerator F hζ S₀ b.2.2.2 ^ 6)
  let Nc := (sourcePrimeExponentNorm F S₀ b.1.val : ℂ) ^ (-(1 / 2 : ℂ) - ξ)
  let Nl := (sourcePrimeExponentNorm F S₀ b.2.1 : ℂ) ^ (-1 - 3 * ξ)
  let Nk := (sourcePrimeExponentNorm F S₀ b.2.2.1 : ℂ) ^ (-w)
  let Nr := (sourcePrimeExponentNorm F S₀ b.2.2.2 : ℂ) ^ (-(6 : ℂ) * z)
  have hΓΦ := sourceGammaTwo_finiteF_product F hζ S₀ b.1 b.2.1 b.2.2.1 b.2.2.2 u hu T hc hk hA
  have hΘ := reflectionThetaValue_prefix F hζ S₀ hS η A T hA
  have hNc := sourcePrimeExponentNorm_cpow_prefix F S₀ b.1.val (-(1 / 2 : ℂ) - ξ) T hc
  have hNl := sourcePrimeExponentNorm_cpow_prefix F S₀ b.2.1 (-1 - 3 * ξ) T hl
  have hNk := sourcePrimeExponentNorm_cpow_prefix F S₀ b.2.2.1 (-w) T hk
  have hNr := sourcePrimeExponentNorm_cpow_prefix F S₀ b.2.2.2 (-(6 : ℂ) * z) T hr
  calc
    _ = Γ * Θ * Φ * Nc * Nl * Nk * Nr := rfl
    _ = (Γ * Φ) * Θ * Nc * Nl * Nk * Nr := by ac_rfl
    _ = ∏ P : T, f P.val (a P.val) := by
      dsimp only [Γ, Θ, Φ, Nc, Nl, Nk, Nr]
      rw [hΓΦ, hΘ, hNc, hNl, hNk, hNr]
      simp only [← Finset.prod_mul_distrib]
      apply Finset.prod_congr rfl
      intro P _
      change _ = sourceLocalEulerTerm F hζ S₀ hS η u hu ξ w z P.val (a P.val)
      simp only [sourceLocalEulerTerm, A, Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul]
      rfl
    _ = _ := Finset.prod_coe_sort T (fun P => f P (a P))

end
end ArtinMatthews.SourceEulerAssembly
