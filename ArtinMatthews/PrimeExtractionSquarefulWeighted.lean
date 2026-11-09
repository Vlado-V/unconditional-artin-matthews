module

public import ArtinMatthews.PrimeExtractionWeightBounds
public import ArtinMatthews.PrimeExtractionSquarefulAsymptotic


set_option backward.privateInPublic true
@[expose] public section

/-! Removal of the actual squareful rough contribution, with the literal
marking array and genuine Hecke theta and Dirichlet coefficients. -/

namespace ArtinMatthews

open Filter OAI.SevenEighths
open scoped BigOperators Asymptotics

noncomputable def markedSquarefulThetaSum {ι : Type*} [Fintype ι]
    (e : ι → ℝ) (η : HeckeFamily.Character) {q : ℕ} (χ : DirichletCharacter ℂ q)
    (G : ℝ → ℕ → ℂ) (Φ : ℝ → ℝ) (T γ x : ℝ) : ℂ :=
  ∑ n ∈ roughNonsquarefreeUpTo ⌊T * x⌋₊ (x ^ γ),
    (Φ (((n - 1 : ℕ) : ℝ) / x) : ℂ) * (literalMarkedArrayWeight e x (n - 1) : ℂ) *
      G x (n - 1) * (idealThetaCoeff η n * χ n)

/-- The squareful terms in Proposition 8.1 are negligible with arbitrary
logarithmic saving. The arithmetic array and coefficient bounds are proved;
the only core assumption is the stated uniform bound on G. -/
theorem markedSquarefulThetaSum_isLittleO {ι : Type*} [Fintype ι]
    (e : ι → ℝ) (he : ∀ i, 0 < e i)
    (η : HeckeFamily.Character) {q : ℕ} (χ : DirichletCharacter ℂ q)
    (G : ℝ → ℕ → ℂ) {CG : ℝ} (hCG : 0 ≤ CG)
    (hG : ∀ᶠ x : ℝ in atTop, ∀ u : ℕ, ‖G x u‖ ≤ CG)
    (Φ : ℝ → ℝ) (hΦ : Continuous Φ) {T γ : ℝ} (hT : 0 ≤ T) (hγ : 0 < γ) (A : ℝ) :
    markedSquarefulThetaSum e η χ G Φ T γ =o[atTop]
      (fun x : ℝ => x * (Real.log x) ^ (-A)) := by
  classical
  obtain ⟨CΦ, hCΦ⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (hΦ.continuousOn : ContinuousOn Φ (Set.Icc 0 T))
  have hCΦ0 : 0 ≤ CΦ := (norm_nonneg (Φ 0)).trans (hCΦ 0 ⟨le_rfl, hT⟩)
  let W := (2 / Real.log 2) ^ Fintype.card ι
  let D := (2 : ℝ) ^ ⌈2 / γ⌉₊
  let C := CΦ * W * CG * D
  have hbound : ∀ᶠ x : ℝ in atTop,
      ‖markedSquarefulThetaSum e η χ G Φ T γ x‖ ≤ C * roughNonsquarefreeCount T γ x := by
    filter_upwards [literalMarkedArrayWeight_bound_eventually e he,
      idealThetaCoeff_rough_bound_eventually T hγ, hG, eventually_gt_atTop (0 : ℝ)]
      with x hW htheta hGx hx
    have hterm : ∀ n ∈ roughNonsquarefreeUpTo ⌊T * x⌋₊ (x ^ γ),
        ‖(Φ (((n - 1 : ℕ) : ℝ) / x) : ℂ) * (literalMarkedArrayWeight e x (n - 1) : ℂ) *
          G x (n - 1) * (idealThetaCoeff η n * χ n)‖ ≤ C := by
      intro n hn
      obtain ⟨hnrange, hn0, hnrough, _⟩ := Finset.mem_filter.mp hn
      have hnT : (n : ℝ) ≤ T * x :=
        (Nat.cast_le.mpr (Nat.le_of_lt_succ (Finset.mem_range.mp hnrange))).trans
          (Nat.floor_le (mul_nonneg hT hx.le))
      have harg : ((n - 1 : ℕ) : ℝ) / x ∈ Set.Icc 0 T :=
        ⟨div_nonneg (Nat.cast_nonneg _) hx.le,
          (div_le_iff₀ hx).mpr ((Nat.cast_le.mpr (Nat.sub_le n 1)).trans hnT)⟩
      have hphi : ‖(Φ (((n - 1 : ℕ) : ℝ) / x) : ℂ)‖ ≤ CΦ := by
        simpa only [Complex.norm_real] using hCΦ _ harg
      have hweight : ‖(literalMarkedArrayWeight e x (n - 1) : ℂ)‖ ≤ W := by
        simpa only [Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (literalMarkedArrayWeight_nonneg e x (n - 1))] using hW (n - 1)
      have hthetaN : ‖idealThetaCoeff η n * χ n‖ ≤ D := htheta n hn0 hnT hnrough η q χ
      simp only [norm_mul]
      change _ ≤ CΦ * W * CG * D
      gcongr
      · exact hGx _
      · simpa only [norm_mul] using hthetaN
    calc
      _ ≤ ∑ n ∈ roughNonsquarefreeUpTo ⌊T * x⌋₊ (x ^ γ),
          ‖(Φ (((n - 1 : ℕ) : ℝ) / x) : ℂ) * (literalMarkedArrayWeight e x (n - 1) : ℂ) *
            G x (n - 1) * (idealThetaCoeff η n * χ n)‖ := norm_sum_le _ _
      _ ≤ ∑ _n ∈ roughNonsquarefreeUpTo ⌊T * x⌋₊ (x ^ γ), C := Finset.sum_le_sum hterm
      _ = C * roughNonsquarefreeCount T γ x := by
        simp only [Finset.sum_const, nsmul_eq_mul, roughNonsquarefreeCount, mul_comm]
  have hbigO : markedSquarefulThetaSum e η χ G Φ T γ =O[atTop] roughNonsquarefreeCount T γ := by
    apply Asymptotics.IsBigO.of_bound C
    filter_upwards [hbound] with x hx
    simpa only [Real.norm_of_nonneg (show 0 ≤ roughNonsquarefreeCount T γ x from Nat.cast_nonneg _)]
      using hx
  exact hbigO.trans_isLittleO (roughNonsquarefreeCount_isLittleO hT hγ A)

end ArtinMatthews
