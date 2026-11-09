module

public import ArtinMatthews.SourceLocalHeightComparison
public import ArtinMatthews.SourceKPAdelicHeightCompact


set_option backward.privateInPublic true
@[expose] public section

/-! Full adelic height comparability under right multiplication, including
a uniform two-sided bound on actual compact matrix sets. -/
namespace ArtinMatthews
open NumberField IsDedekindDomain Matrix Matrix.GeneralLinearGroup Filter
open SourceArchJacquet
open scoped NumberField MatrixGroups AdeleRing BigOperators
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

theorem sourceKPAdelicHeight_mul_le (g h : GL (Fin 2) 𝔸[K]) :
    sourceKPAdelicHeight K hζ (g * h) ≤
      sourceKPAdelicHeightConstant K hζ h * sourceKPAdelicHeight K hζ g := by
  let I := fun v : InfinitePlace K => sourceArchHeight (sourceKPAdelicBaseComplexAt K hζ v (g * h))
  let F := fun P : HeightOneSpectrum (𝓞 K) =>
    sourceKPFiniteMatrixHeight K P (sourceKPAdelicBaseFiniteAt K P (g * h))
  let CI := fun v : InfinitePlace K => sourceArchMatrixHeightConstant (sourceKPAdelicBaseComplexAt K hζ v h)
  let CF := fun P : HeightOneSpectrum (𝓞 K) =>
    sourceKPFiniteMatrixHeightConstant K P (sourceKPAdelicBaseFiniteAt K P h)
  let GI := fun v : InfinitePlace K => sourceArchHeight (sourceKPAdelicBaseComplexAt K hζ v g)
  let GF := fun P : HeightOneSpectrum (𝓞 K) =>
    sourceKPFiniteMatrixHeight K P (sourceKPAdelicBaseFiniteAt K P g)
  have hIloc (v : InfinitePlace K) : I v ≤ CI v * GI v := by
    dsimp only [I, CI, GI]
    rw [map_mul]
    exact sourceArchHeight_mul_le _ _
  have hFloc (P : HeightOneSpectrum (𝓞 K)) : F P ≤ CF P * GF P := by
    dsimp only [F, CF, GF]
    rw [map_mul]
    exact sourceKPFiniteMatrixHeight_mul_le K P _ _
  have hI : (∏ v, I v ^ v.mult) ≤ (∏ v, CI v ^ v.mult) * (∏ v, GI v ^ v.mult) := by
    calc
      _ ≤ ∏ v, (CI v * GI v) ^ v.mult := by
        apply Finset.prod_le_prod₀
        · intro v _
          exact pow_nonneg (sourceArchHeight_pos _).le _
        · intro v _
          exact pow_le_pow_left₀ (sourceArchHeight_pos _).le (hIloc v) _
      _ = _ := by simp only [mul_pow, Finset.prod_mul_distrib]
  have hFs : F.HasFiniteMulSupport := sourceKPAdelicFiniteHeight_finite_support K (g * h)
  have hCFs : CF.HasFiniteMulSupport := sourceKPAdelicHeightConstant_finite_support K h
  have hGFs : GF.HasFiniteMulSupport := sourceKPAdelicFiniteHeight_finite_support K g
  have hF : (∏ᶠ P, F P) ≤ (∏ᶠ P, CF P) * (∏ᶠ P, GF P) := by
    calc
      _ ≤ ∏ᶠ P, CF P * GF P := finprod_le_finprod₀ hFs
        (fun P => (sourceKPFiniteMatrixHeight_pos K P _).le) (hCFs.mul hGFs) hFloc
      _ = _ := finprod_mul_distrib hCFs hGFs
  have hF0 : 0 ≤ ∏ᶠ P, F P := by
    rw [finprod_eq_prod _ hFs]
    exact Finset.prod_nonneg (fun P _ => (sourceKPFiniteMatrixHeight_pos K P _).le)
  have hCI0 : 0 ≤ ∏ v, CI v ^ v.mult :=
    Finset.prod_nonneg (fun v _ => pow_nonneg (sourceArchMatrixHeightConstant_pos _).le _)
  have hGI0 : 0 ≤ ∏ v, GI v ^ v.mult :=
    Finset.prod_nonneg (fun v _ => pow_nonneg (sourceArchHeight_pos _).le _)
  calc
    sourceKPAdelicHeight K hζ (g * h) = (∏ v, I v ^ v.mult) * (∏ᶠ P, F P) := by
      simpa only [I, F, sourceKPFiniteMatrixHeight, sourceKPBottomMax] using
        sourceKPAdelicHeight_product K hζ (g * h)
    _ ≤ ((∏ v, CI v ^ v.mult) * (∏ v, GI v ^ v.mult)) *
        ((∏ᶠ P, CF P) * (∏ᶠ P, GF P)) := mul_le_mul hI hF hF0 (mul_nonneg hCI0 hGI0)
    _ = sourceKPAdelicHeightConstant K hζ h *
        ((∏ v, GI v ^ v.mult) * (∏ᶠ P, GF P)) := by
      change ((∏ v, CI v ^ v.mult) * (∏ v, GI v ^ v.mult)) *
        ((∏ᶠ P, CF P) * (∏ᶠ P, GF P)) =
        ((∏ v, CI v ^ v.mult) * (∏ᶠ P, CF P)) * ((∏ v, GI v ^ v.mult) * (∏ᶠ P, GF P))
      ring
    _ = _ := by
      congr 1
      exact (sourceKPAdelicHeight_product K hζ g).symm

def sourceKPAdelicHeightComparisonConstant (h : GL (Fin 2) 𝔸[K]) : ℝ :=
  max (sourceKPAdelicHeightConstant K hζ h) (sourceKPAdelicHeightConstant K hζ h⁻¹)

theorem sourceKPAdelicHeightComparisonConstant_pos (h : GL (Fin 2) 𝔸[K]) :
    0 < sourceKPAdelicHeightComparisonConstant K hζ h :=
  (sourceKPAdelicHeightConstant_pos K hζ h).trans_le (le_max_left _ _)

theorem sourceKPAdelicHeight_mul_comparison (g h : GL (Fin 2) 𝔸[K]) :
    (sourceKPAdelicHeightComparisonConstant K hζ h)⁻¹ * sourceKPAdelicHeight K hζ g ≤
      sourceKPAdelicHeight K hζ (g * h) ∧
    sourceKPAdelicHeight K hζ (g * h) ≤
      sourceKPAdelicHeightComparisonConstant K hζ h * sourceKPAdelicHeight K hζ g := by
  let C := sourceKPAdelicHeightComparisonConstant K hζ h
  have hC : 0 < C := sourceKPAdelicHeightComparisonConstant_pos K hζ h
  have hu : sourceKPAdelicHeight K hζ (g * h) ≤ C * sourceKPAdelicHeight K hζ g :=
    (sourceKPAdelicHeight_mul_le K hζ g h).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (sourceKPAdelicHeight_pos K hζ g).le)
  have hl : sourceKPAdelicHeight K hζ g ≤ C * sourceKPAdelicHeight K hζ (g * h) := by
    have hback := sourceKPAdelicHeight_mul_le K hζ (g * h) h⁻¹
    rw [mul_inv_cancel_right] at hback
    exact hback.trans (mul_le_mul_of_nonneg_right (le_max_right _ _)
      (sourceKPAdelicHeight_pos K hζ (g * h)).le)
  refine ⟨?_, hu⟩
  calc
    C⁻¹ * sourceKPAdelicHeight K hζ g ≤ C⁻¹ * (C * sourceKPAdelicHeight K hζ (g * h)) :=
      mul_le_mul_of_nonneg_left hl (inv_nonneg.mpr hC.le)
    _ = _ := by rw [← mul_assoc, inv_mul_cancel₀ hC.ne', one_mul]

theorem sourceKPAdelicHeight_mul_uniform_on_compact
    (S : Set (GL (Fin 2) 𝔸[K])) (hS : IsCompact S) :
    ∃ B : ℝ, 0 < B ∧ ∀ h ∈ S, ∀ g : GL (Fin 2) 𝔸[K],
      B⁻¹ * sourceKPAdelicHeight K hζ g ≤ sourceKPAdelicHeight K hζ (g * h) ∧
        sourceKPAdelicHeight K hζ (g * h) ≤ B * sourceKPAdelicHeight K hζ g := by
  obtain ⟨B₁, hB₁, hbound₁⟩ := sourceKPAdelicHeightConstant_bounded K hζ S hS
  obtain ⟨B₂, _, hbound₂⟩ := sourceKPAdelicHeightConstant_bounded K hζ
    (Inv.inv '' S) (hS.image continuous_inv)
  let B := max B₁ B₂
  have hB : 0 < B := hB₁.trans_le (le_max_left _ _)
  refine ⟨B, hB, ?_⟩
  intro h hh g
  have hC : sourceKPAdelicHeightComparisonConstant K hζ h ≤ B :=
    max_le ((hbound₁ h hh).trans (le_max_left _ _))
      ((hbound₂ h⁻¹ ⟨h, hh, rfl⟩).trans (le_max_right _ _))
  obtain ⟨hl, hu⟩ := sourceKPAdelicHeight_mul_comparison K hζ g h
  refine ⟨?_, hu.trans (mul_le_mul_of_nonneg_right hC (sourceKPAdelicHeight_pos K hζ g).le)⟩
  exact (mul_le_mul_of_nonneg_right
    (inv_anti₀ (sourceKPAdelicHeightComparisonConstant_pos K hζ h) hC)
    (sourceKPAdelicHeight_pos K hζ g).le).trans hl

end
end ArtinMatthews
