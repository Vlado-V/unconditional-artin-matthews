module

public import ArtinMatthews.SourceQuadraticDualDyadicWeights


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews.SourceEulerAssembly
open NumberField IsDedekindDomain QuadraticScale StandardAdelic
open scoped NumberField Classical BigOperators
noncomputable section

variable (F : Type) [Field F] [NumberField F] [IsTotallyComplex F]
variable (S₀ : Finset (HeightOneSpectrum (𝓞 F))) {ζ : F} (hζ : IsPrimitiveRoot ζ 12)
local notation "E" => SourcePrimeExponents F S₀
local notation "q" => sourcePrimeExponentNorm F S₀

theorem sourceQuadraticDualEulerRowSum_weighted_bound {α : ℝ} (hα : 1 ≤ α)
    (htrace : traceBadPlaces F ⊆ sourceHilbertSet F S₀)
    (hE : QuadraticHeckeSieveExponentBound (sourceQuadraticDyadicEnergy F S₀ hζ) α)
    (η : ℝ) (hη : 0 < η) :
    ∃ C : ℝ, 0 < C ∧ ∀ L K P : ℝ, 0 < L → 1 ≤ K → 1 ≤ P →
      ∀ rows cols : Finset E,
      (∀ a ∈ rows, sourceReflectionIsSquarefree a ∧ L ≤ (q a : ℝ) ∧ (q a : ℝ) ≤ K) →
      (∀ b ∈ cols, sourceReflectionIsSquarefree b ∧ (q b : ℝ) ≤ 2 * P) →
      ∀ u v w : E → ℂ, (∀ b ∈ cols, ‖v b‖ ≤ ‖u b‖) →
      (∀ b ∈ cols, ‖w b‖ ≤ ‖u b‖) → ∀ s : ℂ, 0 ≤ s.re → s.re ≤ 1 →
      ‖sourceQuadraticDualEulerRowSum F S₀ hζ rows cols v w s‖ ≤
        C * (2 * K * P) ^ η * (2 * P) ^ η * (sourceReflectionDyadLength K : ℝ) *
          (2 * P * L ^ (-(s.re / 2)) + (2 : ℝ) ^ α * K ^ (α - s.re / 2)) *
          coeffMass cols u := by
  obtain ⟨C, hC, hbound⟩ := sourceQuadraticDualEulerRowSum_interval_bound F S₀ hζ
    htrace hE η hη
  refine ⟨C, hC, ?_⟩
  intro L K P hL hK hP rows cols hrows hcols u v w hv hw s hs hs₁
  let len := sourceReflectionDyadLength K
  let block (j : ℕ) := rows.filter (fun a => Nat.log 2 (q a) = j)
  let R (j : ℕ) := (2 : ℝ) ^ j
  let W := 2 * P * L ^ (-(s.re / 2)) + (2 : ℝ) ^ α * K ^ (α - s.re / 2)
  let B := C * (2 * K * P) ^ η * (2 * P) ^ η * W * coeffMass cols u
  have hmass : 0 ≤ coeffMass cols u := coeffMass_nonneg _ _
  have hB : 0 ≤ B := by
    dsimp [B, W]
    positivity
  have hK0 := zero_lt_one.trans_le hK
  have hfloor : ⌊K⌋₊ ≠ 0 := by
    have h : (1 : ℕ) ≤ ⌊K⌋₊ := Nat.le_floor (by simpa using hK)
    omega
  have hR (j : ℕ) : 1 ≤ R j := one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2)
  have hRK (j : ℕ) (hj : j ∈ Finset.range len) : R j ≤ K := by
    have hj' : j ≤ Nat.log 2 ⌊K⌋₊ := by
      have h := Finset.mem_range.mp hj
      unfold len sourceReflectionDyadLength at h
      omega
    calc
      _ ≤ (2 : ℝ) ^ Nat.log 2 ⌊K⌋₊ := pow_le_pow_right₀ (by norm_num) hj'
      _ ≤ (⌊K⌋₊ : ℝ) := by exact_mod_cast Nat.pow_log_le_self 2 hfloor
      _ ≤ _ := Nat.floor_le hK0.le
  have hblockRows (j : ℕ) (a : E) (ha : a ∈ block j) :
      sourceReflectionIsSquarefree a ∧ R j ≤ (q a : ℝ) ∧ (q a : ℝ) ≤ 2 * R j := by
    obtain ⟨har, hj⟩ := Finset.mem_filter.mp ha
    have h := sourceReflectionDyad_bounds (sourcePrimeExponentNorm_pos F S₀ a)
    rw [hj] at h
    exact ⟨(hrows a har).1, h.1, h.2.le⟩
  have hblock (j : ℕ) (hj : j ∈ Finset.range len) :
      ‖sourceQuadraticDualEulerRowSum F S₀ hζ (block j) cols v w s‖ ≤ B := by
    by_cases hempty : block j = ∅
    · simpa only [hempty, sourceQuadraticDualEulerRowSum, Finset.sum_empty, norm_zero] using hB
    obtain ⟨a, ha⟩ := Finset.nonempty_iff_ne_empty.mpr hempty
    have hLR : L ≤ 2 * R j := (hrows a (Finset.mem_filter.mp ha).1).2.1.trans
      (hblockRows j a ha).2.2
    have hr0 : 0 < R j := zero_lt_one.trans_le (hR j)
    have hb := hbound (R j) (2 * R j) P hr0 (by linarith [hR j]) hP
      (block j) cols (hblockRows j) hcols u v w hv hw s hs
    have hwgt := quadraticDual_dyadic_weights (α := α) (σ := s.re) hL hr0 (hRK j hj) hLR
      (zero_le_one.trans hP) hs hs₁ (by linarith)
    calc
      _ ≤ C * (2 * R j * P) ^ η * (2 * P) ^ η *
          (R j ^ (-(s.re / 2)) * (P + (2 * R j) ^ α)) * coeffMass cols u := by
        convert hb using 1
        ring
      _ ≤ B := by
        dsimp only [B, W]
        apply mul_le_mul_of_nonneg_right _ (coeffMass_nonneg _ _)
        apply mul_le_mul _ hwgt (by positivity) (by positivity)
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        apply mul_le_mul_of_nonneg_left _ hC.le
        exact Real.rpow_le_rpow (by positivity)
          (mul_le_mul_of_nonneg_right (by linarith [hRK j hj]) (zero_le_one.trans hP)) hη.le
  have hsplit : sourceQuadraticDualEulerRowSum F S₀ hζ rows cols v w s =
      ∑ j ∈ Finset.range len, sourceQuadraticDualEulerRowSum F S₀ hζ (block j) cols v w s := by
    unfold sourceQuadraticDualEulerRowSum
    exact (Finset.sum_fiberwise_of_maps_to (fun a ha =>
      Finset.mem_range.mpr (sourceReflectionDyad_lt_length (hrows a ha).2.2)) _).symm
  calc
    _ = ‖∑ j ∈ Finset.range len, sourceQuadraticDualEulerRowSum F S₀ hζ (block j) cols v w s‖ :=
      congrArg norm hsplit
    _ ≤ ∑ j ∈ Finset.range len, ‖sourceQuadraticDualEulerRowSum F S₀ hζ (block j) cols v w s‖ :=
      norm_sum_le _ _
    _ ≤ ∑ _j ∈ Finset.range len, B := Finset.sum_le_sum hblock
    _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul, Finset.card_range]; dsimp [B, len]; ring

end
end ArtinMatthews.SourceEulerAssembly
