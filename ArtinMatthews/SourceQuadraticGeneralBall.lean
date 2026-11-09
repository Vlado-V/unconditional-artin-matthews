module

public import ArtinMatthews.SourceQuadraticSieveBall


set_option backward.privateInPublic true
@[expose] public section

/-! Sum the proved row dyads with their original oriented coefficients.
The logarithmic count of dyads is absorbed in half of the requested
power loss. The exponent is unchanged and columns remain on the original norm ball. -/
namespace ArtinMatthews.SourceEulerAssembly

open NumberField IsDedekindDomain VaryingKummerAnalytic StandardAdelic
open scoped NumberField Classical BigOperators

noncomputable section

variable (F : Type) [Field F] [NumberField F] [IsTotallyComplex F]
variable (S₀ : Finset (HeightOneSpectrum (𝓞 F))) {ζ : F} (hζ : IsPrimitiveRoot ζ 12)
variable (htrace : traceBadPlaces F ⊆ sourceHilbertSet F S₀)
include htrace
local notation "E" => ReflectionSquarefreeExponents F S₀
local notation "q" => sourcePrimeExponentNorm F S₀

theorem sourceQuadraticSieveBall_of_exponent {α : ℝ}
    (hE : QuadraticHeckeSieveExponentBound (sourceQuadraticDyadicEnergy F S₀ hζ) α) :
    ∀ ε : ℝ, 0 < ε → ∃ B : ℝ, 0 < B ∧ ∀ D N : ℝ, 1 ≤ D → 1 ≤ N →
      ∀ (rows cols : Finset E),
        (∀ e ∈ rows, (q e.val : ℝ) ≤ D) → (∀ e ∈ cols, (q e.val : ℝ) ≤ N) →
        ∀ a : E → ℂ, sourceQuadraticSieveRowEnergy F S₀ hζ rows cols a ≤
          B * (D + N ^ α) * (D * N) ^ ε * ∑ e ∈ cols, ‖a e‖ ^ 2 := by
  intro ε hε
  let η := ε / 2
  have hη : 0 < η := half_pos hε
  obtain ⟨C, hC, hCbound⟩ := hE η hη
  obtain ⟨H, hH, hlog⟩ := sourceReflectionLogPower_le (K := 2) (m := 1)
    (by norm_num) zero_le_one hη 1 (by decide)
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨C * (H / Real.log 2), by positivity, ?_⟩
  intro D N hD hN rows cols hr hc a
  let len := sourceReflectionDyadLength D
  let index (e : E) := Nat.log 2 (q e.val)
  let block (j : ℕ) := rows.filter (fun e => index e = j)
  let M (j : ℕ) := (2 : ℝ) ^ j
  let mass : ℝ := ∑ e ∈ cols, ‖a e‖ ^ 2
  have hmass : 0 ≤ mass := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hDN : 1 ≤ D * N := one_le_mul_of_one_le_of_one_le hD hN
  have hD0 := zero_lt_one.trans_le hD
  have hfloor : ⌊D⌋₊ ≠ 0 := by
    have h : (1 : ℕ) ≤ ⌊D⌋₊ := Nat.le_floor (by simpa using hD)
    omega
  have hM (j : ℕ) : 1 ≤ M j := one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2)
  have hMle (j : ℕ) (hj : j ∈ Finset.range len) : M j ≤ D := by
    have hj' : j ≤ Nat.log 2 ⌊D⌋₊ := by
      have h := Finset.mem_range.mp hj
      unfold len sourceReflectionDyadLength at h
      omega
    calc
      _ ≤ (2 : ℝ) ^ Nat.log 2 ⌊D⌋₊ := pow_le_pow_right₀ (by norm_num) hj'
      _ ≤ (⌊D⌋₊ : ℝ) := by exact_mod_cast Nat.pow_log_le_self 2 hfloor
      _ ≤ _ := Nat.floor_le hD0.le
  have hsplit : sourceQuadraticSieveRowEnergy F S₀ hζ rows cols a =
      ∑ j ∈ Finset.range len, sourceQuadraticSieveRowEnergy F S₀ hζ (block j) cols a := by
    unfold sourceQuadraticSieveRowEnergy
    exact (Finset.sum_fiberwise_of_maps_to (fun e he =>
      Finset.mem_range.mpr (sourceReflectionDyad_lt_length (hr e he))) _).symm
  have hblock (j : ℕ) (hj : j ∈ Finset.range len) :
      sourceQuadraticSieveRowEnergy F S₀ hζ (block j) cols a ≤
        C * (D * N) ^ η * (D + N ^ α) * mass := by
    have hrows (e : E) (he : e ∈ block j) :
        M j ≤ (q e.val : ℝ) ∧ (q e.val : ℝ) ≤ 2 * M j := by
      have hh := sourceReflectionDyad_bounds (sourcePrimeExponentNorm_pos F S₀ e.val)
      have he' : Nat.log 2 (q e.val) = j := (Finset.mem_filter.mp he).2
      rw [he'] at hh
      exact ⟨hh.1, hh.2.le⟩
    have hbase := sourceQuadraticDyadicEnergy_admissible F S₀ hζ htrace (hM j) hN
    have hp : (M j * N) ^ η ≤ (D * N) ^ η :=
      Real.rpow_le_rpow (by positivity [hM j])
        (mul_le_mul_of_nonneg_right (hMle j hj) (zero_le_one.trans hN)) hη.le
    calc
      _ ≤ sourceQuadraticDyadicEnergy F S₀ hζ (M j) N * mass :=
        hbase.2 _ _ hrows hc a
      _ ≤ C * (M j * N) ^ η * (M j + N ^ α) * mass :=
        mul_le_mul_of_nonneg_right (hCbound (M j) N (hM j) hN) hmass
      _ ≤ _ := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul (mul_le_mul_of_nonneg_left hp hC.le)
            (add_le_add_left (hMle j hj) _) (by positivity [hM j, hN]) (by positivity)) hmass
  have hlen : (len : ℝ) ≤ (H / Real.log 2) * (D * N) ^ η := by
    have h := hlog D hD
    rw [pow_one, Real.rpow_one] at h
    calc
      _ ≤ Real.log (2 * D) / Real.log 2 := sourceReflectionDyadLength_le_log hD
      _ ≤ H * D ^ η / Real.log 2 := div_le_div_of_nonneg_right h hl2.le
      _ = (H / Real.log 2) * D ^ η := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow hD0.le (le_mul_of_one_le_right hD0.le hN) hη.le) (by positivity)
  have hpow : (D * N) ^ η * (D * N) ^ η = (D * N) ^ ε := by
    rw [← Real.rpow_add (zero_lt_one.trans_le hDN), show η + η = ε from add_halves ε]
  calc
    _ = _ := hsplit
    _ ≤ ∑ _j ∈ Finset.range len, C * (D * N) ^ η * (D + N ^ α) * mass :=
      Finset.sum_le_sum hblock
    _ = (len : ℝ) * (C * (D * N) ^ η * (D + N ^ α) * mass) := by
      simp only [Finset.sum_const, nsmul_eq_mul, Finset.card_range]
    _ ≤ ((H / Real.log 2) * (D * N) ^ η) *
        (C * (D * N) ^ η * (D + N ^ α) * mass) :=
      mul_le_mul_of_nonneg_right hlen (by positivity [hD, hN])
    _ = _ := by rw [← hpow]; ring

end
end ArtinMatthews.SourceEulerAssembly
