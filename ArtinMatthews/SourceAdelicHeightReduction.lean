module

public import ArtinMatthews.SourceAdelicShortRow
public import ArtinMatthews.SourceAdelicHeightBottomBound


set_option backward.privateInPublic true
@[expose] public section

/-! The actual source height has a positive rational-translate lower bound
on every determinant-one adelic matrix. -/
namespace ArtinMatthews
open NumberField IsDedekindDomain MeasureTheory Matrix Matrix.GeneralLinearGroup
open OAI.RepresentationTheory.Weil.AdelicSplitting SourceArchJacquet
open scoped NumberField AdeleRing MatrixGroups Classical BigOperators
noncomputable section

variable (F : Type) [Field F] [NumberField F] {ζ : F} (hζ : IsPrimitiveRoot ζ 12)

theorem sourceKPAdelicSL2_rational_height_lower :
    ∃ c : ℝ, 0 < c ∧ ∀ g : SL(2, 𝔸[F]), ∃ γ : SL(2, F),
      c ≤ sourceKPAdelicHeight F hζ
        (GeneralLinearGroup.map (algebraMap F 𝔸[F]) γ.toGL * g.toGL) := by
  obtain ⟨R, hR, hshort⟩ := sourceSL2Adelic_uniform_short_row F
  let c := ∏ v : InfinitePlace F, (1 / (2 * R ^ 2)) ^ v.mult
  have hc : 0 < c := Finset.prod_pos (fun v _ => pow_pos (by positivity) _)
  refine ⟨c, hc, fun g => ?_⟩
  obtain ⟨q, hq, hfin₀, hfin₁, harch⟩ := hshort g
  obtain ⟨γ, hγ₀, hγ₁⟩ := sourceSL2_exists_bottom_row q hq
  let h : SL(2, 𝔸[F]) := Matrix.SpecialLinearGroup.map (algebraMap F 𝔸[F]) γ * g
  have h₀ : h 1 0 = (sourceRationalAdelicRow F g q).1 := by
    change (∑ i : Fin 2, algebraMap F 𝔸[F] (γ 1 i) * g i 0) = _
    simp only [Fin.sum_univ_two, hγ₀, hγ₁, sourceRationalAdelicRow]
  have h₁ : h 1 1 = (sourceRationalAdelicRow F g q).2 := by
    change (∑ i : Fin 2, algebraMap F 𝔸[F] (γ 1 i) * g i 1) = _
    simp only [Fin.sum_univ_two, hγ₀, hγ₁, sourceRationalAdelicRow]
  have he : h.toGL = GeneralLinearGroup.map (algebraMap F 𝔸[F]) γ.toGL * g.toGL := by
    apply Units.ext
    rfl
  refine ⟨γ, ?_⟩
  rw [← he]
  apply sourceSL2Adelic_height_lower_of_bottom_bound F hζ h hR
  · simpa only [h₀] using hfin₀
  · simpa only [h₁] using hfin₁
  · simpa only [h₀, h₁] using harch

end
end ArtinMatthews
