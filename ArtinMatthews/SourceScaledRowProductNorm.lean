module

public import ArtinMatthews.SourceReducedFractionNorm
public import ArtinMatthews.SourceAdditiveCompactBox


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews.SourcePhysical
open NumberField NumberField.InfinitePlace IsDedekindDomain AllowedGenerators Set
open scoped NumberField Classical BigOperators
noncomputable section

variable (F : Type) [Field F] [NumberField F]
variable (S : Finset (HeightOneSpectrum (𝓞 F)))
local notation "A" => SLocalAdditiveCompletionSpace F S

/-- The actual product norm on all additive completion coordinates. -/
def sourceAdditiveProductNorm (x : A) : ℝ :=
  (∏ w : InfinitePlace F, ‖x.1 w‖ ^ w.mult) * ∏ p : S, ‖x.2 p‖

theorem sourceAdditiveProductNorm_continuous : Continuous (sourceAdditiveProductNorm F S) := by
  unfold sourceAdditiveProductNorm
  exact (continuous_finsetProd _ (fun w _ =>
    (((continuous_apply w).comp continuous_fst).norm.pow w.mult))).mul
      (continuous_finsetProd _ (fun p _ => ((continuous_apply p).comp continuous_snd).norm))

theorem sourceAdditiveProductNorm_mul (x y : A) :
    sourceAdditiveProductNorm F S (x * y) =
      sourceAdditiveProductNorm F S x * sourceAdditiveProductNorm F S y := by
  simp only [sourceAdditiveProductNorm, Prod.fst_mul, Prod.snd_mul, Pi.mul_apply,
    norm_mul, mul_pow, Finset.prod_mul_distrib]
  ac_rfl

theorem sourceAdditiveProductNorm_unitPoint (a : SWholeUnits F S) :
    sourceAdditiveProductNorm F S (sourceSLocalUnitAdditivePoint F S a) = sLocalNorm F S a :=
  (sLocalNorm_eq_prod F S a).symm

variable (S₀ : Finset (HeightOneSpectrum (𝓞 F)))
variable {ζ : F} (hζ : IsPrimitiveRoot ζ 12)
local notation "T" => sourceHilbertSet F S₀
local notation "U" => SourceNonzeroFrequency F S₀

include hζ in
theorem sourceAdditiveProductNorm_exterior (m : U) :
    sourceAdditiveProductNorm F T (sLocalRingDiagonal F T (m.val : F)) =
      (sourcePrimeExponentNorm F S₀ (sourceElementExponents F S₀ m.val m.property) : ℝ) := by
  change sourceAdditiveProductNorm F T (sourceSLocalUnitAdditivePoint F T
    (sWholeDiagonal F T (sourceNonzeroFrequencyFieldUnit F S₀ m))) = _
  rw [sourceAdditiveProductNorm_unitPoint]
  exact sourceSInteger_fieldSNorm_eq F S₀ hζ m.val m.property

/-- One compact-box constant controls the genuine exterior ideal norms at all positive scales. -/
theorem sourceScaledLatticeRows_exteriorNorm_bound
    (B : Set (SLocalAdditiveCompletionSpace F T)) (hB : IsCompact B) :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ N : ℝ, 0 < N → ∀ m : U,
      m.val ∈ sourceScaledLatticeRows F S₀ hζ B N →
      (sourcePrimeExponentNorm F S₀ (sourceElementExponents F S₀ m.val m.property) : ℝ) ≤ K * N := by
  obtain ⟨K, hK⟩ := hB.bddAbove_image (sourceAdditiveProductNorm_continuous F T).continuousOn
  refine ⟨max 1 K, le_max_left _ _, fun N hN m hm => ?_⟩
  obtain ⟨y, hy, he⟩ := hm
  change sourceSLocalUnitAdditivePoint F T (sLocalPositiveScaling F hζ T N) * y =
    sLocalRingDiagonal F T (m.val : F) at he
  rw [← sourceAdditiveProductNorm_exterior F S₀ hζ m, ← he, sourceAdditiveProductNorm_mul,
    sourceAdditiveProductNorm_unitPoint, sLocalPositiveScaling_norm F hζ T hN, mul_comm N]
  exact mul_le_mul_of_nonneg_right ((hK (mem_image_of_mem _ hy)).trans (le_max_right _ _)) hN.le

end
end ArtinMatthews.SourcePhysical
