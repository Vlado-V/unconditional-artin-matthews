module

public import ArtinMatthews.SourceReflectionPowerful
public import ArtinMatthews.NumberFieldIdealLinearCount
public import ArtinMatthews.SourcePrimeNormSummability


set_option backward.privateInPublic true
@[expose] public section

/-! Fixed-field counts for the actual ideal rows in Section 04. -/
namespace ArtinMatthews.SourceEulerAssembly
open NumberField IsDedekindDomain
open scoped NumberField Classical BigOperators
noncomputable section

variable (F : Type) [Field F] [NumberField F]

theorem exists_sourceReflectionIdealCard_le :
    ∃ C : ℝ, 0 < C ∧ ∀ (X : ℝ), 1 ≤ X → ∀ A : Finset (Ideal (𝓞 F)),
      (∀ I ∈ A, (I.absNorm : ℝ) ≤ X) → (A.card : ℝ) ≤ C * X := by
  obtain ⟨C, hC, hc⟩ := exists_idealNormCount_linear F
  refine ⟨C, hC, fun X hX A hA => ?_⟩
  let N := ⌊X⌋₊
  have hN : 1 ≤ N := Nat.le_floor (by exact_mod_cast hX)
  let : Fintype {I : Ideal (𝓞 F) // I.absNorm ≤ N} :=
    (Ideal.finite_setOfPred_absNorm_le (S := 𝓞 F) N).fintype
  have hcard := Nat.card_le_card_of_injective
    (fun I : {I // I ∈ A} => (⟨I.val, Nat.le_floor (hA I.val I.property)⟩ :
      {I : Ideal (𝓞 F) // I.absNorm ≤ N}))
    (fun I J h => Subtype.ext (congrArg (fun K : {I : Ideal (𝓞 F) // I.absNorm ≤ N} => K.val) h))
  have hcA : A.card ≤ idealNormCount F N := by
    simpa only [Nat.card_eq_fintype_card, Fintype.card_coe, idealNormCount] using hcard
  exact (Nat.cast_le.mpr hcA).trans ((hc N hN).trans
    (mul_le_mul_of_nonneg_left (Nat.floor_le (zero_le_one.trans hX)) hC.le))

theorem sourceReflectionIdealSquareCube_norm {I : Ideal (𝓞 F)}
    (hI : sourceReflectionPowerfulIdeal F I) :
    ((sourceReflectionIdealSquare F I).absNorm : ℝ) ^ 2 *
      ((sourceReflectionIdealCube F I).absNorm : ℝ) ^ 3 = (I.absNorm : ℝ) := by
  exact_mod_cast (by
    rw [← map_pow, ← map_pow, ← map_mul, sourceReflectionIdealSquareCube F hI] :
      (sourceReflectionIdealSquare F I).absNorm ^ 2 *
        (sourceReflectionIdealCube F I).absNorm ^ 3 = I.absNorm)

theorem exists_sourceReflectionPowerfulIdealCard_le :
    ∃ C : ℝ, 0 < C ∧ ∀ (X : ℝ), 1 ≤ X → ∀ A : Finset (Ideal (𝓞 F)),
      (∀ I ∈ A, sourceReflectionPowerfulIdeal F I ∧ (I.absNorm : ℝ) ≤ X) →
      (A.card : ℝ) ≤ C * Real.sqrt X := by
  obtain ⟨B, hB, hb⟩ := exists_sourceReflectionIdealCard_le F
  let W (S : {I : Ideal (𝓞 F) // I ≠ ⊥}) : ℝ := (S.val.absNorm : ℝ) ^ (-3 / 2 : ℝ)
  have hs : Summable W := by
    have h := VaryingKummerAnalytic.HeckeIdealMobius.normSeries_summable F (by norm_num : 0 < (1 / 2 : ℝ))
    simpa only [W, show -(1 + (1 / 2 : ℝ)) = (-3 / 2 : ℝ) by norm_num] using h
  have hw (S : {I : Ideal (𝓞 F) // I ≠ ⊥}) : 0 ≤ W S :=
    Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hsum₀ : 0 ≤ ∑' S, W S := tsum_nonneg hw
  refine ⟨B * (1 + ∑' S, W S), mul_pos hB (by linarith), ?_⟩
  intro X hX A hA
  let cube (I : Ideal (𝓞 F)) : {I : Ideal (𝓞 F) // I ≠ ⊥} :=
    ⟨sourceReflectionIdealCube F I, sourceReflectionIdealCube_ne_bot F I⟩
  have hX₀ : 0 ≤ X := zero_le_one.trans hX
  have hfiber (S : {I : Ideal (𝓞 F) // I ≠ ⊥}) (hS : S ∈ A.image cube) :
      ((A.filter (fun I => cube I = S)).card : ℝ) ≤ B * Real.sqrt X * W S := by
    let T := A.filter (fun I => cube I = S)
    have hs₀ : (0 : ℝ) < S.val.absNorm := by
      exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr S.property)
    have hbnd (I : Ideal (𝓞 F)) (hI : I ∈ T) :
        ((sourceReflectionIdealSquare F I).absNorm : ℝ) ≤ Real.sqrt (X / (S.val.absNorm : ℝ) ^ 3) := by
      obtain ⟨hIA, hIS⟩ := Finset.mem_filter.mp hI
      have hq := sourceReflectionIdealSquareCube_norm F (hA I hIA).1
      have hIS' : sourceReflectionIdealCube F I = S.val := congrArg Subtype.val hIS
      rw [hIS'] at hq
      apply (Real.le_sqrt (Nat.cast_nonneg _) (div_nonneg hX₀ (pow_nonneg hs₀.le _))).2
      exact (le_div_iff₀ (pow_pos hs₀ _)).2 (hq.le.trans (hA I hIA).2)
    obtain ⟨I, hI, hIS⟩ := Finset.mem_image.mp hS
    have hX' : 1 ≤ Real.sqrt (X / (S.val.absNorm : ℝ) ^ 3) := by
      have hN : 1 ≤ (sourceReflectionIdealSquare F I).absNorm :=
        Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr
          (sourceReflectionIdealSquare_ne_bot F I))
      exact (Nat.one_le_cast.mpr hN).trans (hbnd I (Finset.mem_filter.mpr ⟨hI, hIS⟩))
    have hcard : (T.image (sourceReflectionIdealSquare F)).card = T.card := by
      apply Finset.card_image_of_injOn
      intro I hIT J hJT hsq
      obtain ⟨hIA, hIS⟩ := Finset.mem_filter.mp hIT
      obtain ⟨hJA, hJS⟩ := Finset.mem_filter.mp hJT
      have hcube : sourceReflectionIdealCube F I = sourceReflectionIdealCube F J :=
        congrArg Subtype.val (hIS.trans hJS.symm)
      calc
        I = sourceReflectionIdealSquare F I ^ 2 * sourceReflectionIdealCube F I ^ 3 :=
          (sourceReflectionIdealSquareCube F (hA I hIA).1).symm
        _ = sourceReflectionIdealSquare F J ^ 2 * sourceReflectionIdealCube F J ^ 3 := by
          rw [hsq, hcube]
        _ = J := sourceReflectionIdealSquareCube F (hA J hJA).1
    have he : Real.sqrt (X / (S.val.absNorm : ℝ) ^ 3) = Real.sqrt X * W S := by
      rw [Real.sqrt_div hX₀, div_eq_mul_inv, Real.sqrt_eq_rpow ((S.val.absNorm : ℝ) ^ 3),
        ← Real.rpow_natCast_mul hs₀.le]
      congr 1
      rw [← Real.rpow_neg hs₀.le]
      congr 1
      norm_num
    calc
      (T.card : ℝ) = ((T.image (sourceReflectionIdealSquare F)).card : ℝ) := by rw [hcard]
      _ ≤ B * Real.sqrt (X / (S.val.absNorm : ℝ) ^ 3) := by
        apply hb _ hX'
        intro R hR
        obtain ⟨J, hJ, rfl⟩ := Finset.mem_image.mp hR
        exact hbnd J hJ
      _ = _ := by rw [he]; ring
  calc
    (A.card : ℝ) = ∑ S ∈ A.image cube, ((A.filter (fun I => cube I = S)).card : ℝ) := by
      exact_mod_cast Finset.card_eq_sum_card_image cube A
    _ ≤ ∑ S ∈ A.image cube, B * Real.sqrt X * W S := Finset.sum_le_sum hfiber
    _ = B * Real.sqrt X * ∑ S ∈ A.image cube, W S := (Finset.mul_sum _ _ _).symm
    _ ≤ B * Real.sqrt X * (∑' S, W S) :=
      mul_le_mul_of_nonneg_left (hs.sum_le_tsum _ (fun S _ => hw S)) (by positivity)
    _ ≤ (B * (1 + ∑' S, W S)) * Real.sqrt X := by
      calc
        _ ≤ B * Real.sqrt X * (1 + ∑' S, W S) :=
          mul_le_mul_of_nonneg_left (le_add_of_nonneg_left zero_le_one) (by positivity)
        _ = _ := by ring

end
end ArtinMatthews.SourceEulerAssembly
