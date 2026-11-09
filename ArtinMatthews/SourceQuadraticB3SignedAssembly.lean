module

public import ArtinMatthews.SourceQuadraticDualFiniteErrors
public import ArtinMatthews.SourceQuadraticSmallError
public import ArtinMatthews.SourceQuadraticDiagonalBlock


set_option backward.privateInPublic true
@[expose] public section

/-! Exact signed components of the original B3 block. The original Small
estimate and residue cancellation use all common pairs. The extra diagonal
dual residue therefore remains explicitly subtracted. -/
namespace ArtinMatthews.SourceEulerAssembly
open NumberField IsDedekindDomain QuadraticScale
open scoped NumberField Classical
noncomputable section

variable (F : Type) [Field F] [NumberField F]
variable (S₀ : Finset (HeightOneSpectrum (𝓞 F))) {ζ : F} (hζ : IsPrimitiveRoot ζ 12)
local notation "E" => SourcePrimeExponents F S₀

def sourceQuadraticCommonPairBlock (H : E → ℂ) (cols : Finset E)
    (u : E → ℂ) (g : E) : ℂ :=
  ∑ p ∈ (cols ×ˢ cols).filter (fun p : E × E => p.1 ⊓ p.2 = g),
    star (u p.1) * u p.2 * H ((p.1 - g) + (p.2 - g))

def sourceQuadraticNonzeroResidualBlock (H : E → ℂ) (cols : Finset E)
    (u : E → ℂ) (g : E) : ℂ :=
  ∑ p ∈ (cols ×ˢ cols).filter (fun p : E × E => p.1 ⊓ p.2 = g),
    if (p.1 - g) + (p.2 - g) ≠ 0 then
      star (u p.1) * u p.2 * H ((p.1 - g) + (p.2 - g)) else 0

theorem sourceQuadraticCommonPairBlock_add (H J : E → ℂ) (cols : Finset E)
    (u : E → ℂ) (g : E) :
    sourceQuadraticCommonPairBlock F S₀ (fun e => H e + J e) cols u g =
      sourceQuadraticCommonPairBlock F S₀ H cols u g +
        sourceQuadraticCommonPairBlock F S₀ J cols u g := by
  simp only [sourceQuadraticCommonPairBlock, mul_add, Finset.sum_add_distrib]

theorem sourceQuadraticCommonPairBlock_sub (H J : E → ℂ) (cols : Finset E)
    (u : E → ℂ) (g : E) :
    sourceQuadraticCommonPairBlock F S₀ (fun e => H e - J e) cols u g =
      sourceQuadraticCommonPairBlock F S₀ H cols u g -
        sourceQuadraticCommonPairBlock F S₀ J cols u g := by
  simp only [sourceQuadraticCommonPairBlock, mul_sub, Finset.sum_sub_distrib]

theorem sourceQuadraticCommonPairBlock_split (H : E → ℂ) (cols : Finset E)
    (u : E → ℂ) (g : E) :
    sourceQuadraticCommonPairBlock F S₀ H cols u g =
      sourceQuadraticZeroResidualBlock F S₀ H cols u g +
        sourceQuadraticNonzeroResidualBlock F S₀ H cols u g := by
  simp only [sourceQuadraticCommonPairBlock, sourceQuadraticZeroResidualBlock,
    sourceQuadraticNonzeroResidualBlock, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro p _
  by_cases h : (p.1 - g) + (p.2 - g) = 0 <;> simp [h]

theorem sourceQuadraticNonzeroResidualBlock_eq_offDiagonal (H : E → ℂ)
    (cols : Finset E) (u : E → ℂ) (g : E) :
    sourceQuadraticNonzeroResidualBlock F S₀ H cols u g =
      ∑ p ∈ (cols ×ˢ cols).filter (fun p : E × E => p.1 ⊓ p.2 = g ∧ p.1 ≠ p.2),
        star (u p.1) * u p.2 * H ((p.1 - g) + (p.2 - g)) := by
  rw [sourceQuadraticNonzeroResidualBlock, ← Finset.sum_filter, Finset.filter_filter]
  apply Finset.sum_congr
  · apply Finset.filter_congr
    intro p _
    constructor
    · rintro ⟨hg, hn⟩
      exact ⟨hg, mt (sourceQuadraticPair_residual_eq_zero_iff F S₀ p.1 p.2 g hg).mpr hn⟩
    · rintro ⟨hg, hn⟩
      exact ⟨hg, mt (sourceQuadraticPair_residual_eq_zero_iff F S₀ p.1 p.2 g hg).mp hn⟩
  · intro _ _
    rfl

variable [IsTotallyComplex F]

theorem sourceQuadraticB3Block_signed_components {M K σ τ : ℝ}
    (hM : 0 < M) (hK : 0 ≤ K) (hσ : 0 < σ) (hσone : σ < 1)
    (hτ : 0 < τ) (hτone : τ < 1)
    (cols : Finset E) (u : E → ℂ) (g : E)
    (hcols : ∀ b ∈ cols, sourceReflectionIsSquarefree b) :
    sourceQuadraticB3Block F S₀ hζ (sourceQuadraticB2Rows F S₀ M K) cols
        (sourceQuadraticB2RowWeight F S₀ M) u g =
      sourceQuadraticZeroResidualBlock F S₀
          (sourceQuadraticBlockIdealFull F S₀ hζ M g) cols u g +
        sourceQuadraticNonzeroResidualBlock F S₀
          (sourceQuadraticDualDivisorError F S₀ hζ M K τ g) cols u g +
        sourceQuadraticNonzeroResidualBlock F S₀
          (sourceQuadraticDualDivisorTail F S₀ hζ M K g) cols u g -
        sourceQuadraticOriginalSmallErrorBlock F S₀ hζ M K σ cols u g +
        sourceQuadraticCommonPairBlock F S₀ (fun e =>
          sourceQuadraticDualDivisorResidue F S₀ hζ M K g e -
          sourceQuadraticOriginalSmallResidue F S₀ hζ M K g e) cols u g -
        sourceQuadraticZeroResidualBlock F S₀
          (sourceQuadraticDualDivisorResidue F S₀ hζ M K g) cols u g := by
  rw [sourceQuadraticB3Block_eq_full_sub_small F S₀ hζ hM cols u g hcols]
  simp only [sourceQuadraticZeroResidualBlock, sourceQuadraticNonzeroResidualBlock,
    sourceQuadraticOriginalSmallErrorBlock, sourceQuadraticCommonPairBlock,
    ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro p hp
  obtain ⟨hpair, hg⟩ := Finset.mem_filter.mp hp
  obtain ⟨hb, hc⟩ := Finset.mem_product.mp hpair
  rw [sourceQuadraticBlockIdealSmall_eq_error_add_residue F S₀ hζ hM hK hσ hσone]
  by_cases hz : (p.1 - g) + (p.2 - g) = 0
  · simp [hz]
    ring
  · rw [sourceQuadraticBlockIdealFull_eq_error_residue_tail F S₀ hζ hM hτ hτone K g _
      (sourceQuadraticPair_residual_data F S₀ p.1 p.2 g (hcols _ hb) (hcols _ hc) hg).2.2.2 hz]
    simp [hz]
    ring

end
end ArtinMatthews.SourceEulerAssembly
