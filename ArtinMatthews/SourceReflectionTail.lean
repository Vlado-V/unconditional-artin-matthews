module

public import ArtinMatthews.SourceReflectionSeries
public import ArtinMatthews.SourceReflectionActiveBudget


set_option backward.privateInPublic true
@[expose] public section

/-! Absolute tail estimate including dyads with cutoff below one. -/
namespace ArtinMatthews.SourceEulerAssembly
open NumberField IsDedekindDomain
open scoped NumberField Classical BigOperators
noncomputable section

variable (F : Type) [Field F] [NumberField F]
variable (S₀ : Finset (HeightOneSpectrum (𝓞 F)))
variable {ζ : F} (hζ : IsPrimitiveRoot ζ 12)
variable {U : Type} (A : SourceReflectionExpansionData F S₀ U)

local notation "Prime" => SourceExteriorPrime F S₀
local notation "E" => SourcePrimeExponents F S₀
local notation "q" => sourcePrimeExponentNorm F S₀

theorem sourceReflectionTailBranch_le {Z P D δ N σ M : ℝ}
    (hZ : 0 < Z) (hσ : 1 / 2 < σ) (hN : σ ≤ N) (hM : 0 ≤ M)
    (h d : E) (f : Finset Prime) (u : U)
    (htL : sourceReflectionTermScale F S₀ Z f d ≤ sourceReflectionLength Z P D)
    (hp : ∀ (a n : E) (x : ℝ), 0 < x → ‖A.profile h f a n u x‖ ≤ M * x ^ (-N)) :
    ‖sourceReflectionSelectedBranch F S₀ hζ A Z h d f u
      (fun Q => sourceReflectionCutoff Z P D δ < Q)‖ ≤
      (M * sourceReflectionLength Z P D ^ σ * sourceReflectionTailScale Z P D δ ^ (-(N - σ))) *
        (sourceReflectionFrozenFactors F S₀ f σ *
          (sourceReflectionCubeSeries F S₀ σ * sourceReflectionColumnSeries F S₀ σ)) := by
  let L := sourceReflectionLength Z P D
  let J := sourceReflectionTailScale Z P D δ
  let t := sourceReflectionTermScale F S₀ Z f d
  let R := sourceReflectionCutoff Z P D δ
  let T := M * L ^ σ * J ^ (-(N - σ))
  have ht : 0 < t := sourceReflectionTermScale_pos F S₀ hZ f d
  have hL : 0 < L := ht.trans_le htL
  have hJ : 0 < J := (Real.rpow_pos_of_pos hZ δ).trans_le (le_max_left _ _)
  have hT : 0 ≤ T := by dsimp [T]; positivity
  have hs := sourceReflectionDirichlet_hasSum F S₀ f hσ
  unfold sourceReflectionSelectedBranch
  refine (norm_tsum_le_tsum_norm
    (sourceReflectionSelectedBranch_norm_summable F S₀ hζ A hZ h d f u (fun Q => R < Q))).trans ?_
  calc
    _ ≤ ∑' i : SourceReflectionTermIndex F S₀ f, T * sourceReflectionDirichletTerm F S₀ f σ i := by
      apply Summable.tsum_le_tsum
      · intro i
        let Q := sourceReflectionTermLength F S₀ i.1.val i.2.1 i.2.2.val
        have hQ : 1 ≤ Q := sourceReflectionTermLength_one_le F S₀ _ _ _
        have hQ₀ := zero_lt_one.trans_le hQ
        by_cases hi : R < Q
        · rw [ite_eq_left hi]
          apply sourceReflectionExpansionTerm_norm_le F S₀ hζ A Z h d f u i T σ
          change ‖A.profile h f i.1.val i.2.1 u (Q / t)‖ ≤ T * Q ^ (-σ)
          have hx : (t / Q) ^ σ ≤ L ^ σ * Q ^ (-σ) := by
            rw [Real.div_rpow ht.le hQ₀.le, Real.rpow_neg hQ₀.le, div_eq_mul_inv]
            exact mul_le_mul_of_nonneg_right (Real.rpow_le_rpow ht.le htL (by linarith))
              (inv_nonneg.mpr (Real.rpow_nonneg hQ₀.le _))
          calc
            _ ≤ M * (Q / t) ^ (-N) := hp _ _ _ (div_pos hQ₀ ht)
            _ ≤ M * (J ^ (-(N - σ)) * (t / Q) ^ σ) := mul_le_mul_of_nonneg_left
              (sourceReflectionTailKernel_le hZ ht htL hQ hi hN) hM
            _ ≤ M * (J ^ (-(N - σ)) * (L ^ σ * Q ^ (-σ))) :=
              mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hx (Real.rpow_nonneg hJ.le _)) hM
            _ = _ := by dsimp [T]; ring
        · rw [ite_eq_right hi, norm_zero]
          exact mul_nonneg hT (sourceReflectionDirichletTerm_nonneg F S₀ f σ i)
      · exact sourceReflectionSelectedBranch_norm_summable F S₀ hζ A hZ h d f u (fun Q => R < Q)
      · exact hs.summable.mul_left T
    _ = _ := by rw [tsum_mul_left, hs.tsum_eq]

variable [Fintype U]

theorem exists_sourceReflectionTailRow_le {δ δ₁ N σ : ℝ}
    (hδ₁ : 0 < δ₁) (hσ : 1 / 2 < σ) (hN : σ ≤ N) :
    ∃ C : ℝ, 0 < C ∧ ∀ Z P D : ℝ, 0 < Z → 1 ≤ P → 1 ≤ D →
      ∀ h d : E, sourceReflectionIsPowerful h → (q h : ℝ) ≤ 2 * P → (q d : ℝ) ≤ 2 * D →
      ‖sourceReflectionSelectedRow F S₀ hζ A Z h d (fun Q => sourceReflectionCutoff Z P D δ < Q)‖ ≤
        C * P ^ δ₁ * sourceReflectionLength Z P D ^ σ * sourceReflectionTailScale Z P D δ ^ (-(N - σ)) := by
  obtain ⟨M, hM, hp⟩ := sourceReflectionProfileDecay F S₀ A (by linarith : 0 < N)
  obtain ⟨C, hC, hc⟩ := exists_sourceReflectionActiveBudget F S₀ hδ₁
  let V := sourceReflectionCubeSeries F S₀ σ * sourceReflectionColumnSeries F S₀ σ
  have hV : 0 ≤ V := sourceReflectionDirichletSeries_nonneg F S₀ σ
  let C₀ := (Fintype.card U : ℝ) * M * V * C * (2 : ℝ) ^ δ₁
  have hC₀ : 0 ≤ C₀ := by dsimp [C₀]; positivity
  refine ⟨1 + C₀, by linarith, ?_⟩
  intro Z P D hZ hP hD h d hh hhP hdD
  let L := sourceReflectionLength Z P D
  let J := sourceReflectionTailScale Z P D δ
  have hL : 0 < L := sourceReflectionLength_pos hZ (zero_lt_one.trans_le hP) (zero_lt_one.trans_le hD)
  have hJ : 0 < J := (Real.rpow_pos_of_pos hZ δ).trans_le (le_max_left _ _)
  let W := (Fintype.card U : ℝ) * M * V * L ^ σ * J ^ (-(N - σ))
  have hW : 0 ≤ W := by dsimp [W]; positivity
  have hterm (f : Finset Prime) (hf : f ∈ sourceReflectionActiveChoices F S₀ h) :
      ‖∑ u : U, sourceReflectionSelectedBranch F S₀ hζ A Z h d f u
        (fun Q => sourceReflectionCutoff Z P D δ < Q)‖ ≤
          W * sourceReflectionFrozenFactors F S₀ f σ := by
    calc
      _ ≤ ∑ _u : U, (M * L ^ σ * J ^ (-(N - σ))) * (sourceReflectionFrozenFactors F S₀ f σ * V) := by
        apply norm_sum_le_of_le
        intro u _
        exact sourceReflectionTailBranch_le F S₀ hζ A hZ hσ hN hM h d f u
          (sourceReflectionTermScale_le F S₀ hZ hh hhP hdD hf) (hp h f · · u)
      _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul, Finset.card_univ, W]; ring
  have hPow : (q h : ℝ) ^ δ₁ ≤ (2 : ℝ) ^ δ₁ * P ^ δ₁ := by
    rw [← Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) (zero_le_one.trans hP)]
    exact Real.rpow_le_rpow (Nat.cast_nonneg _) hhP hδ₁.le
  unfold sourceReflectionSelectedRow
  calc
    _ ≤ ∑ f ∈ sourceReflectionActiveChoices F S₀ h, W * sourceReflectionFrozenFactors F S₀ f σ :=
      norm_sum_le_of_le _ hterm
    _ ≤ W * (C * (q h : ℝ) ^ δ₁) := by
      rw [← Finset.mul_sum]
      exact mul_le_mul_of_nonneg_left (hc h σ (by linarith)) hW
    _ ≤ W * (C * ((2 : ℝ) ^ δ₁ * P ^ δ₁)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hPow hC.le) hW
    _ = C₀ * P ^ δ₁ * L ^ σ * J ^ (-(N - σ)) := by dsimp [W, C₀]; ring
    _ ≤ _ := by
      change C₀ * P ^ δ₁ * L ^ σ * J ^ (-(N - σ)) ≤ (1 + C₀) * P ^ δ₁ * L ^ σ * J ^ (-(N - σ))
      gcongr
      linarith

end
end ArtinMatthews.SourceEulerAssembly
