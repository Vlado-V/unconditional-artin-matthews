module

public import Mathlib.NumberTheory.NumberField.Ideal.Asymptotics
public import ArtinMatthews.SixthExteriorIdealRowClasses


set_option backward.privateInPublic true
@[expose] public section

/-! A genuine linear ideal count from the number-field ideal asymptotic,
and its consequence for the constructed finite S-unit row family. -/
namespace ArtinMatthews
open NumberField Filter IsDedekindDomain NumberField.InfinitePlace NumberField.Units
open scoped NumberField nonZeroDivisors Classical Topology
noncomputable section
variable (K : Type) [Field K] [NumberField K]

def idealNormCount (N : ℕ) : ℕ := Nat.card {I : Ideal (𝓞 K) // I.absNorm ≤ N}

theorem idealNormCount_mono : Monotone (idealNormCount K) := by
  intro n m hnm
  let : Fintype {I : Ideal (𝓞 K) // I.absNorm ≤ m} :=
    (Ideal.finite_setOfPred_absNorm_le (S := 𝓞 K) m).fintype
  exact Nat.card_le_card_of_injective
    (fun I : {I : Ideal (𝓞 K) // I.absNorm ≤ n} =>
      (⟨I.1,I.2.trans hnm⟩ : {I : Ideal (𝓞 K) // I.absNorm ≤ m}))
    (fun _ _ h => Subtype.ext (congrArg
      (fun I : {I : Ideal (𝓞 K) // I.absNorm ≤ m} => I.1) h))

theorem exists_idealNormCount_linear :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 1 ≤ N → (idealNormCount K N : ℝ) ≤ C*N := by
  let A : ℝ := (2 ^ nrRealPlaces K * (2 * Real.pi) ^ nrComplexPlaces K *
    regulator K * classNumber K) / (torsionOrder K * Real.sqrt |discr K|)
  have hev : ∀ᶠ x : ℝ in atTop,
      (Nat.card {I : Ideal (𝓞 K) // (I.absNorm : ℝ) ≤ x} : ℝ) / x < A+1 :=
    (NumberField.Ideal.tendsto_norm_le_div_atTop K).eventually
      (eventually_lt_nhds (lt_add_one A))
  obtain ⟨R,hR⟩ := eventually_atTop.mp hev
  obtain ⟨n₀,hn₀⟩ := exists_nat_gt R
  let C : ℝ := |A|+2+(idealNormCount K n₀ : ℝ)
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C,hC,?_⟩
  intro N hN
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hN)
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  by_cases hlarge : n₀ ≤ N
  · have hx : R ≤ (N : ℝ) := hn₀.le.trans (by exact_mod_cast hlarge)
    have hb : (idealNormCount K N : ℝ) / N < A+1 := by
      simpa only [Nat.cast_le,idealNormCount] using hR N hx
    have hA : A+1 ≤ C := by
      dsimp [C]
      nlinarith [le_abs_self A, (show (0 : ℝ) ≤ (idealNormCount K n₀ : ℝ) from Nat.cast_nonneg _)]
    exact ((div_lt_iff₀ hNpos).mp hb).le.trans (mul_le_mul_of_nonneg_right hA hNpos.le)
  · have hb : (idealNormCount K N : ℝ) ≤ (idealNormCount K n₀ : ℝ) := by
      exact_mod_cast idealNormCount_mono K (Nat.le_of_lt (lt_of_not_ge hlarge))
    have hc : (idealNormCount K n₀ : ℝ) ≤ C := by dsimp [C]; linarith [abs_nonneg A]
    exact hb.trans (hc.trans (le_mul_of_one_le_right hC.le hN1))

theorem exteriorBoundedIdealRows_card_le (S : Finset (HeightOneSpectrum (𝓞 K))) (N : ℕ) :
    (exteriorBoundedIdealRows S N).card ≤ idealNormCount K N := by
  let : Fintype {I : Ideal (𝓞 K) // I.absNorm ≤ N} :=
    (Ideal.finite_setOfPred_absNorm_le (S := 𝓞 K) N).fintype
  have h := Nat.card_le_card_of_injective
    (fun I : {I // I ∈ exteriorBoundedIdealRows S N} =>
      (⟨I.1,((mem_exteriorBoundedIdealRows S N I.1).mp I.2).1⟩ :
        {I : Ideal (𝓞 K) // I.absNorm ≤ N}))
    (fun _ _ h => Subtype.ext (congrArg
      (fun I : {I : Ideal (𝓞 K) // I.absNorm ≤ N} => I.1) h))
  simpa only [Nat.card_eq_fintype_card,Fintype.card_coe,idealNormCount] using h

theorem exists_exteriorIdealRows_linear (S : Finset (HeightOneSpectrum (𝓞 K))) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 1 ≤ N →
      (Fintype.card (ExteriorIdealRowIndex S N) : ℝ) ≤ C*N := by
  obtain ⟨B,hB,hbound⟩ := exists_idealNormCount_linear K
  let w : ℝ := (exteriorUnitSixthRepresentatives S).card
  refine ⟨B*(w+1),mul_pos hB (by dsimp [w]; positivity),?_⟩
  intro N hN
  have hc := exteriorBoundedIdealRows_card_le K S N
  have hcr : ((exteriorBoundedIdealRows S N).card : ℝ) ≤ (idealNormCount K N : ℝ) := by
    exact_mod_cast hc
  have hbc : ((exteriorBoundedIdealRows S N).card : ℝ) ≤ B*N :=
    hcr.trans (hbound N hN)
  have hw : 0 ≤ w := by dsimp [w]; positivity
  rw [exteriorIdealRowIndex_card,Nat.cast_mul]
  change ((exteriorBoundedIdealRows S N).card : ℝ)*w ≤ _
  nlinarith [mul_le_mul_of_nonneg_right hbc hw]

end
end ArtinMatthews
