module

public import ArtinMatthews.SourceReflectionDirichlet


set_option backward.privateInPublic true
@[expose] public section

/-! Absolute convergence and the exact retained/tail split of the
reflected series. The cutoff depends only on the common dyad. -/
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

theorem sourceReflectionProfileDecay {N : ℝ} (hN : 0 < N) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ (h : E) (f : Finset Prime) (a n : E) (u : U) (x : ℝ),
      0 < x → ‖A.profile h f a n u x‖ ≤ M * x ^ (-N) := by
  obtain ⟨α, _, h⟩ := A.profile_derivative
  obtain ⟨M, hM, hb⟩ := h N hN
  refine ⟨M, hM, fun h f a n u x hx => ?_⟩
  have hp := hb h f a n u 0 (by decide) (Real.log x)
  rw [norm_iteratedFDeriv_zero, Real.exp_log hx] at hp
  have hpow : Real.exp (-N * Real.log x) = x ^ (-N) := by
    rw [Real.rpow_def_of_pos hx, mul_comm]
  exact hp.trans (mul_le_mul_of_nonneg_left ((min_le_right _ _).trans_eq hpow) hM)

theorem sourceReflectionExpansionTerm_norm_le
    (Z : ℝ) (h d : E) (f : Finset Prime) (u : U) (i : SourceReflectionTermIndex F S₀ f)
    (B σ : ℝ)
    (hΦ : ‖A.profile h f i.1.val i.2.1 u
        (sourceReflectionTermLength F S₀ i.1.val i.2.1 i.2.2.val /
          sourceReflectionTermScale F S₀ Z f d)‖ ≤
      B * sourceReflectionTermLength F S₀ i.1.val i.2.1 i.2.2.val ^ (-σ)) :
    ‖sourceReflectionExpansionTerm F S₀ hζ A Z h d f i.1.val i.2.1 i.2.2.val u‖ ≤
      B * sourceReflectionDirichletTerm F S₀ f σ i := by
  let a := i.1.val
  let n := i.2.1
  let c := i.2.2.val
  let x := sourceReflectionTermLength F S₀ a n c / sourceReflectionTermScale F S₀ Z f d
  have hn : (0 : ℝ) ≤ q n := Nat.cast_nonneg _
  have hc : (0 : ℝ) < q c := zero_lt_one.trans_le (sourceReflection_norm_one_le F S₀ _)
  have hcolumn : ‖sourceReflectionColumnCoefficient F S₀ A h f a n u c‖ ≤ (q c : ℝ) ^ (-1 / 2 : ℝ) := by
    unfold sourceReflectionColumnCoefficient
    rw [norm_div, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _),
      Real.sqrt_eq_rpow, show (-1 / 2 : ℝ) = -(1 / 2) by ring, Real.rpow_neg hc.le]
    exact (div_le_div_of_nonneg_right (A.column_bound h f a n u c) (Real.rpow_nonneg hc.le _)).trans_eq
      (one_div _)
  have hscalar : ‖A.scalar h f a n u / (q n : ℂ)‖ ≤
      sourceReflectionFrozenWeight F S₀ f a * (q n : ℝ)⁻¹ := by
    rw [norm_div, Complex.norm_natCast, ← div_eq_mul_inv]
    exact div_le_div_of_nonneg_right (A.scalar_bound h f a n u) hn
  have hrow : ‖A.row h f a n u d‖ * ‖sourceReflectionQuadraticSymbol F S₀ hζ d c‖ ≤ 1 := by
    simpa only [mul_one] using mul_le_mul (A.row_bound h f a n u d)
      (sourceReflectionQuadraticSymbol_norm_le_one F S₀ hζ d c) (norm_nonneg _) zero_le_one
  change ‖A.scalar h f a n u / (q n : ℂ) *
    (A.row h f a n u d * sourceReflectionQuadraticSymbol F S₀ hζ d c *
      sourceReflectionColumnCoefficient F S₀ A h f a n u c * A.profile h f a n u x)‖ ≤ _
  simp only [norm_mul]
  have hb := sourceReflectionFrozenWeight_nonneg F S₀ f a
  calc
    _ ≤ (sourceReflectionFrozenWeight F S₀ f a * (q n : ℝ)⁻¹) *
      (1 * (q c : ℝ) ^ (-1 / 2 : ℝ) *
        (B * sourceReflectionTermLength F S₀ a n c ^ (-σ))) := by
      gcongr
    _ = _ := by
      unfold sourceReflectionDirichletTerm
      dsimp only [a, n, c]
      ring

theorem sourceReflectionExpansionTerm_norm_summable {Z : ℝ} (hZ : 0 < Z)
    (h d : E) (f : Finset Prime) (u : U) :
    Summable (fun i : SourceReflectionTermIndex F S₀ f =>
      ‖sourceReflectionExpansionTerm F S₀ hζ A Z h d f i.1.val i.2.1 i.2.2.val u‖) := by
  obtain ⟨M, hM, hp⟩ := sourceReflectionProfileDecay F S₀ A (show (0 : ℝ) < 1 by norm_num)
  let t := sourceReflectionTermScale F S₀ Z f d
  have ht : 0 < t := sourceReflectionTermScale_pos F S₀ hZ f d
  have hs := (sourceReflectionDirichlet_hasSum F S₀ f (show (1 / 2 : ℝ) < 1 by norm_num)).summable
  apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) _ (hs.mul_left (M * t ^ (1 : ℝ)))
  intro i
  let Q := sourceReflectionTermLength F S₀ i.1.val i.2.1 i.2.2.val
  have hQ : 0 < Q := zero_lt_one.trans_le (sourceReflectionTermLength_one_le F S₀ _ _ _)
  apply sourceReflectionExpansionTerm_norm_le F S₀ hζ A Z h d f u i (M * t ^ (1 : ℝ)) 1
  change ‖A.profile h f i.1.val i.2.1 u (Q / t)‖ ≤ M * t ^ (1 : ℝ) * Q ^ (-1 : ℝ)
  calc
    _ ≤ M * (Q / t) ^ (-1 : ℝ) := hp _ _ _ _ _ _ (div_pos hQ ht)
    _ = _ := by
      rw [Real.div_rpow hQ.le ht.le, Real.rpow_neg ht.le, div_inv_eq_mul]
      ring

def sourceReflectionSelectedBranch (Z : ℝ) (h d : E) (f : Finset Prime) (u : U)
    (keep : ℝ → Prop) : ℂ :=
  ∑' i : SourceReflectionTermIndex F S₀ f,
    if keep (sourceReflectionTermLength F S₀ i.1.val i.2.1 i.2.2.val) then
      sourceReflectionExpansionTerm F S₀ hζ A Z h d f i.1.val i.2.1 i.2.2.val u
    else 0

theorem sourceReflectionSelectedBranch_norm_summable {Z : ℝ} (hZ : 0 < Z)
    (h d : E) (f : Finset Prime) (u : U) (keep : ℝ → Prop) :
    Summable (fun i : SourceReflectionTermIndex F S₀ f =>
      ‖if keep (sourceReflectionTermLength F S₀ i.1.val i.2.1 i.2.2.val) then
        sourceReflectionExpansionTerm F S₀ hζ A Z h d f i.1.val i.2.1 i.2.2.val u else 0‖) := by
  apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) _
    (sourceReflectionExpansionTerm_norm_summable F S₀ hζ A hZ h d f u)
  intro i
  split
  · exact le_rfl
  · rw [norm_zero]
    exact norm_nonneg _

theorem sourceReflectionSelectedBranch_split {Z : ℝ} (hZ : 0 < Z)
    (h d : E) (f : Finset Prime) (u : U) (R : ℝ) :
    sourceReflectionSelectedBranch F S₀ hζ A Z h d f u (fun _ => True) =
      sourceReflectionSelectedBranch F S₀ hζ A Z h d f u (fun Q => Q ≤ R) +
        sourceReflectionSelectedBranch F S₀ hζ A Z h d f u (fun Q => R < Q) := by
  unfold sourceReflectionSelectedBranch
  rw [← (sourceReflectionSelectedBranch_norm_summable F S₀ hζ A hZ h d f u (fun Q => Q ≤ R)).of_norm.tsum_add
    (sourceReflectionSelectedBranch_norm_summable F S₀ hζ A hZ h d f u (fun Q => R < Q)).of_norm]
  apply tsum_congr
  intro i
  by_cases hi : sourceReflectionTermLength F S₀ i.1.val i.2.1 i.2.2.val ≤ R
  · simp [hi, not_lt_of_ge hi]
  · simp [hi, lt_of_not_ge hi]

variable [Fintype U]

def sourceReflectionSelectedRow (Z : ℝ) (h d : E) (keep : ℝ → Prop) : ℂ :=
  ∑ f ∈ sourceReflectionActiveChoices F S₀ h, ∑ u : U,
    sourceReflectionSelectedBranch F S₀ hζ A Z h d f u keep

theorem sourceReflectionSelectedRow_split {Z : ℝ} (hZ : 0 < Z) (h d : E) (R : ℝ) :
    sourceReflectionSelectedRow F S₀ hζ A Z h d (fun _ => True) =
      sourceReflectionSelectedRow F S₀ hζ A Z h d (fun Q => Q ≤ R) +
        sourceReflectionSelectedRow F S₀ hζ A Z h d (fun Q => R < Q) := by
  unfold sourceReflectionSelectedRow
  simp only [sourceReflectionSelectedBranch_split F S₀ hζ A hZ h d _ _ R,
    Finset.sum_add_distrib]

end
end ArtinMatthews.SourceEulerAssembly
