module

public import ArtinMatthews.KummerTwistedExceptionalFamily
public import ArtinMatthews.NumberFieldIdealLinearCount


set_option backward.privateInPublic true
@[expose] public section

/-! Actual excluded rows and the arithmetic weighted sums used by the
common probe. Counting is by reduced ideal/S-unit rows; no contour or
Poisson identity is assumed here. -/
namespace ArtinMatthews
open NumberField IsDedekindDomain VaryingKummerAnalytic
open scoped NumberField nonZeroDivisors Classical BigOperators
noncomputable section
variable {K : Type} [Field K] [NumberField K]

def exteriorRowIdealNorm {S : Finset (HeightOneSpectrum (𝓞 K))} {N : ℕ}
    (i : ExteriorIdealRowIndex S N) : ℝ := i.1.1.absNorm

theorem exteriorRow_weight_sum_le_card {S : Finset (HeightOneSpectrum (𝓞 K))} {N : ℕ}
    (T : Finset (ExteriorIdealRowIndex S N)) (U σ : ℝ) (hU : 0 < U) (hσ : 0 ≤ σ)
    (hT : ∀ i ∈ T, U ≤ exteriorRowIdealNorm i) :
    (∑ i ∈ T, (exteriorRowIdealNorm i)^(-σ)) ≤ (T.card : ℝ)*U^(-σ) := by
  calc
    _ ≤ ∑ _i ∈ T, U^(-σ) := by
      apply Finset.sum_le_sum
      intro i hi
      exact Real.rpow_le_rpow_of_nonpos hU (hT i hi) (neg_nonpos.mpr hσ)
    _ = _ := by rw [Finset.sum_const,nsmul_eq_mul]

theorem exteriorRow_weight_sum_of_card_bound {S : Finset (HeightOneSpectrum (𝓞 K))} {N : ℕ}
    (T : Finset (ExteriorIdealRowIndex S N)) (U σ C α : ℝ) (hU : 0 < U) (hσ : 0 ≤ σ)
    (hT : ∀ i ∈ T, U ≤ exteriorRowIdealNorm i) (hc : (T.card : ℝ) ≤ C*U^α) :
    (∑ i ∈ T, (exteriorRowIdealNorm i)^(-σ)) ≤ C*U^(α-σ) := by
  calc
    _ ≤ (T.card : ℝ)*U^(-σ) := exteriorRow_weight_sum_le_card T U σ hU hσ hT
    _ ≤ (C*U^α)*U^(-σ) := mul_le_mul_of_nonneg_right hc (Real.rpow_nonneg hU.le _)
    _ = _ := by rw [mul_assoc,← Real.rpow_add hU,sub_eq_add_neg]

theorem exists_exteriorIdealRows_dyadic_weighted
    (K : Type) [Field K] [NumberField K] (S : Finset (HeightOneSpectrum (𝓞 K))) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ), 1 ≤ N → ∀ U σ : ℝ, 1 ≤ U → (N : ℝ) ≤ 2*U → 0 ≤ σ →
      ∀ T : Finset (ExteriorIdealRowIndex S N), (∀ i ∈ T, U ≤ exteriorRowIdealNorm i) →
      (∑ i ∈ T, (exteriorRowIdealNorm i)^(-σ)) ≤ C*U^(1-σ) := by
  obtain ⟨B,hB,hcount⟩ := exists_exteriorIdealRows_linear K S
  refine ⟨2*B,by positivity,?_⟩
  intro N hN U σ hU hNU hσ T hT
  have hle : (T.card : ℝ) ≤ Fintype.card (ExteriorIdealRowIndex S N) := by
    exact_mod_cast Finset.card_le_univ T
  have hcard : (T.card : ℝ) ≤ B*N :=
    hle.trans (hcount N hN)
  apply exteriorRow_weight_sum_of_card_bound T U σ (2*B) 1 (by linarith) hσ hT
  rw [Real.rpow_one]
  nlinarith [mul_le_mul_of_nonneg_left hNU hB.le]

variable [Algebra K ℂ] [NumberField.IsTotallyComplex K]
variable {M : Ideal (𝓞 K)} {η : EvenIdealRayCharacter K M} {hM : M ≠ ⊥}
variable {ζ : K} {hζ : IsPrimitiveRoot ζ 6}
variable {S : Finset (HeightOneSpectrum (𝓞 K))} {N : ℕ}
variable (d : ∀ i, BoundedKummerTwistedPrimitiveDatum η hM hζ S N i)

def twistedExcludedRows (U r : ℝ) : Finset (ExteriorIdealRowIndex S N) :=
  (Finset.univ.filter (fun i => ¬(d i).character.IsNonprincipal)) ∪
    (twistedPrimitiveExceptionalRows d U r).image Subtype.val

theorem twistedExcludedRows_card_le (hClass : exteriorPrincipalizingPrimes K ⊆ S) (U r : ℝ) :
    ((twistedExcludedRows d U r).card : ℝ) ≤ 1 + (twistedPrimitiveExceptionalRows d U r).card := by
  have h : (twistedExcludedRows d U r).card ≤ 1 + (twistedPrimitiveExceptionalRows d U r).card := by
    exact (Finset.card_union_le _ _).trans (Nat.add_le_add
      (boundedKummerTwistedPrimitiveDatum_principal_count η hM hζ S hClass N d)
      (Finset.card_image_le))
  exact_mod_cast h

omit [NumberField.IsTotallyComplex K] in
theorem twistedExcludedRows_complement {U r : ℝ} {i : ExteriorIdealRowIndex S N}
    (hi : i ∉ twistedExcludedRows d U r) :
    ∃ hnp : (d i).character.IsNonprincipal,
      (⟨i,hnp⟩ : KummerTwistedNonprincipalIndex d) ∉ twistedPrimitiveExceptionalRows d U r := by
  have hnp : (d i).character.IsNonprincipal := by
    by_contra h
    exact hi (Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _,h⟩))
  refine ⟨hnp,?_⟩
  intro h
  exact hi (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨⟨i,hnp⟩,h,rfl⟩))

theorem twistedExcludedRows_weight_bound (hClass : exteriorPrincipalizingPrimes K ⊆ S)
    (V r U σ C : ℝ) (hU : 0 < U) (hσ : 0 ≤ σ)
    (hcount : ((twistedPrimitiveExceptionalRows d V r).card : ℝ) ≤ C*V^(1/2 : ℝ)) :
    (∑ i ∈ (twistedExcludedRows d V r).filter (fun i => U ≤ exteriorRowIdealNorm i),
      (exteriorRowIdealNorm i)^(-σ)) ≤ (1+C*V^(1/2 : ℝ))*U^(-σ) := by
  let T := (twistedExcludedRows d V r).filter (fun i => U ≤ exteriorRowIdealNorm i)
  have hle : (T.card : ℝ) ≤ (twistedExcludedRows d V r).card := by
    exact_mod_cast Finset.card_filter_le (twistedExcludedRows d V r) _
  have hcard : (T.card : ℝ) ≤ 1+C*V^(1/2 : ℝ) :=
    hle.trans
      ((twistedExcludedRows_card_le d hClass V r).trans (by linarith))
  exact (exteriorRow_weight_sum_le_card T U σ hU hσ
    (fun i hi => (Finset.mem_filter.mp hi).2)).trans
      (mul_le_mul_of_nonneg_right hcard (Real.rpow_nonneg hU.le _))

end
end ArtinMatthews
