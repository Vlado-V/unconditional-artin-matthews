module

public import ArtinMatthews.SourceQuadraticB3PoissonBound
public import ArtinMatthews.SourceQuadraticB2ColumnPartition


set_option backward.privateInPublic true
@[expose] public section

/-! Apply the annular B3 input only after decomposing the positive B2
energy into its literal column dyads. The length-one column is included
in the first, trivially bounded block. -/
namespace ArtinMatthews.SourceEulerAssembly

open NumberField IsDedekindDomain QuadraticScale
open scoped NumberField Classical BigOperators

noncomputable section
variable (F : Type) [Field F] [NumberField F]
variable (S₀ : Finset (HeightOneSpectrum (𝓞 F))) {ζ : F} (hζ : IsPrimitiveRoot ζ 12)
variable {G : Type} [Fintype G] [DecidableEq G]

local notation "E" => SourcePrimeExponents F S₀
local notation "q" => sourcePrimeExponentNorm F S₀

theorem exists_sourceQuadraticB2_ball_step (label : E → G) {a δ : ℝ}
    (ha : 1 ≤ a) (hδ : 0 < δ) (hpoisson : SourceQuadraticB3PoissonBound F S₀ hζ label a) :
    ∃ B : ℝ, 1 ≤ B ∧ ∀ M N L H : ℝ, 1 ≤ M → 1 ≤ N → 1 ≤ L → L ≤ N →
      1 ≤ H → 2 * N * (M * N) ^ δ ≤ M →
      let K := poissonCutoff M N δ
      sourceQuadraticSmoothedB2Norm F S₀ hζ M K L ≤
        B * (M * N) ^ (δ * (a + 3 / 2)) *
          (sourceQuadraticSmoothedB2Norm F S₀ hζ M K (L / H) +
            H ^ 5 * poissonMainScale M N a) := by
  obtain ⟨B₀, hB₀, hstep⟩ := exists_sourceQuadraticB2AnnularStep F S₀ hζ label ha hδ hpoisson
  obtain ⟨C, hC, hcount⟩ := exists_sourceReflectionExteriorCard_le F S₀
  obtain ⟨D, hD, hlog⟩ := sourceReflectionLogPower_le (K := 2) (m := 1)
    (by norm_num) zero_le_one hδ 1 (by decide)
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  let A := B₀ + 5 * C ^ 2 + 1
  let D₀ := 1 + D / Real.log 2
  have hA : 1 ≤ A := by dsimp [A]; nlinarith
  have hD₀ : 1 ≤ D₀ := by dsimp [D₀]; linarith [div_pos hD hl2]
  refine ⟨D₀ * A, one_le_mul_of_one_le_of_one_le hD₀ hA, ?_⟩
  intro M N L H hM hN hL hLN hH hsep K
  let T := M * N
  let rows := sourceQuadraticB2Rows F S₀ M K
  let cols := sourceQuadraticB2Columns F S₀ L
  let w := sourceQuadraticB2RowWeight F S₀ M
  let I := Finset.range (sourceReflectionDyadLength L)
  let index (b : E) := sourceQuadraticPoissonColumnDyad (q b)
  let block (j : ℕ) := cols.filter (fun b => index b = j)
  let main := poissonMainScale M N a
  let tail := sourceQuadraticSmoothedB2Norm F S₀ hζ M K (L / H)
  let Z := T ^ (δ * (a + 1 / 2)) * (tail + H ^ 5 * main)
  have hM0 := zero_lt_one.trans_le hM
  have hN0 := zero_lt_one.trans_le hN
  have hT : 1 ≤ T := one_le_mul_of_one_le_of_one_le hM hN
  have hT0 := zero_lt_one.trans_le hT
  have hmain : 0 ≤ main := poissonMainScale_nonneg hM0.le hN0.le a
  have htail : 0 ≤ tail := sourceQuadraticB2Norm_nonneg F S₀ hζ _ _ _
  have hZ : 0 ≤ Z := by dsimp [Z]; positivity
  have hmainM : M ≤ main := by
    change M ≤ M + N + N ^ (2 * a - 1) * M ^ (1 - a)
    have hp : 0 ≤ N ^ (2 * a - 1) * M ^ (1 - a) := by positivity
    linarith
  have hH5 : 1 ≤ H ^ (5 : ℕ) := one_le_pow₀ hH
  have hMZ : M ≤ Z := by
    have hloss : 1 ≤ T ^ (δ * (a + 1 / 2)) :=
      Real.one_le_rpow hT (mul_nonneg hδ.le (by linarith))
    exact hmainM.trans <| (le_mul_of_one_le_left hmain hH5).trans <|
      (le_add_of_nonneg_left htail).trans <|
        le_mul_of_one_le_left (by positivity) hloss
  have hcols (b : E) (hb : b ∈ cols) :
      (q b : ℝ) ≤ L ∧ sourceReflectionIsSquarefree b :=
    (sourceQuadratic_mem_B2Columns F S₀ (zero_le_one.trans hL) b).mp hb
  have hi (b : E) (hb : b ∈ cols) : index b ∈ I := by
    apply Finset.mem_range.mpr
    exact (Nat.log_mono_right (Nat.sub_le (q b) 1)).trans_lt
      (sourceReflectionDyad_lt_length (hcols b hb).1)
  have hrowsCard : (rows.card : ℝ) ≤ C * (5 * M / 2) :=
    hcount _ (by linarith) rows (fun d hd =>
      ((sourceQuadratic_mem_B2Rows F S₀ hM0.le d).mp hd).1)
  have hblock (u : E → ℂ) (j : ℕ) (_hj : j ∈ I) :
      sourceQuadraticB2Energy F S₀ hζ rows (block j) w u ≤
        (A * Z) * coeffMass (block j) u := by
    by_cases hj0 : j = 0
    · have hsmall (b : E) (hb : b ∈ block j) : (q b : ℝ) ≤ 2 := by
        have hindex : sourceQuadraticPoissonColumnDyad (q b) = 0 := by
          simpa only [hj0] using (Finset.mem_filter.mp hb).2
        simpa only [pow_zero, mul_one] using sourceQuadraticPoissonColumnDyad_upper
          (sourcePrimeExponentNorm_pos F S₀ b) hindex
      have hcard := hcount 2 (by norm_num) (block j) hsmall
      have hA₀ : 5 * C ^ 2 ≤ A := by dsimp [A]; linarith
      calc
        _ ≤ (rows.card * (block j).card : ℝ) * coeffMass (block j) u :=
          sourceQuadraticB2Energy_crude F S₀ hζ rows (block j) w
            (fun _ _ => sourceQuadraticB2Bump_le_one _) u
        _ ≤ ((C * (5 * M / 2)) * (C * 2)) * coeffMass (block j) u :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul hrowsCard hcard (Nat.cast_nonneg _) (by positivity)) (coeffMass_nonneg _ _)
        _ = (5 * C ^ 2 * M) * coeffMass (block j) u := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_right
          (mul_le_mul hA₀ hMZ hM0.le (zero_le_one.trans hA)) (coeffMass_nonneg _ _)
    · by_cases hnon : (block j).Nonempty
      · obtain ⟨b, hb⟩ := hnon
        let P := (2 : ℝ) ^ j
        have hP : 1 ≤ P := one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2)
        have hdyad (c : E) (hc : c ∈ block j) :
            P < (q c : ℝ) ∧ (q c : ℝ) ≤ 2 * P := by
          have heq : sourceQuadraticPoissonColumnDyad (q c) = j := (Finset.mem_filter.mp hc).2
          exact ⟨sourceQuadraticPoissonColumnDyad_lower hj0 heq,
            sourceQuadraticPoissonColumnDyad_upper (sourcePrimeExponentNorm_pos F S₀ c) heq⟩
        have hPL : P ≤ L := (hdyad b hb).1.le.trans (hcols b (Finset.mem_filter.mp hb).1).1
        have hh := hstep M N L H P hM hN hL hLN hH hP hPL hsep (block j) u (by
          intro c hc
          have hcm := hcols c (Finset.mem_filter.mp hc).1
          exact ⟨hcm.2, (hdyad c hc).1, (hdyad c hc).2, hcm.1⟩)
        have hB₀A : B₀ ≤ A := by dsimp [A]; nlinarith
        exact hh.trans (mul_le_mul_of_nonneg_right
          (by
            calc
              _ = B₀ * Z := by dsimp [Z]; ring
              _ ≤ A * Z := mul_le_mul_of_nonneg_right hB₀A hZ)
          (coeffMass_nonneg _ _))
      · have he : block j = ∅ := Finset.not_nonempty_iff_eq_empty.mp hnon
        simp only [he, sourceQuadraticB2Energy, coeffMass, rowValue, Finset.sum_empty,
          norm_zero, zero_pow (by decide : (2 : ℕ) ≠ 0), mul_zero, Finset.sum_const_zero, le_refl]
  have hIcard : (I.card : ℝ) ≤ D₀ * T ^ δ := by
    have hh := hlog L hL
    rw [pow_one, Real.rpow_one] at hh
    calc
      _ ≤ Real.log (2 * L) / Real.log 2 := by
        simpa only [I, Finset.card_range] using sourceReflectionDyadLength_le_log hL
      _ ≤ D * L ^ δ / Real.log 2 := div_le_div_of_nonneg_right hh hl2.le
      _ ≤ D * T ^ δ / Real.log 2 := by
        apply div_le_div_of_nonneg_right _ hl2.le
        exact mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow (zero_le_one.trans hL)
            (hLN.trans (le_mul_of_one_le_left hN0.le hM)) hδ.le) hD.le
      _ ≤ _ := by
        dsimp [D₀]
        have hh := Real.rpow_nonneg hT0.le δ
        calc
          _ = (D / Real.log 2) * T ^ δ := by ring
          _ ≤ (1 + D / Real.log 2) * T ^ δ :=
            mul_le_mul_of_nonneg_right (by linarith) hh
  apply sourceQuadraticB2Norm_le_of_weighted_energy F S₀ hζ rows w L
    (fun _ _ => sourceQuadraticB2Bump_nonneg _) (by positivity)
  intro u
  have hsum : (∑ j ∈ I, coeffMass (block j) u) = coeffMass cols u :=
    Finset.sum_fiberwise_of_maps_to hi (fun b => ‖u b‖ ^ 2)
  have hcombine : T ^ δ * T ^ (δ * (a + 1 / 2)) = T ^ (δ * (a + 3 / 2)) := by
    rw [← Real.rpow_add hT0]
    congr 1
    ring
  calc
    _ ≤ I.card * ∑ j ∈ I, sourceQuadraticB2Energy F S₀ hζ rows (block j) w u :=
      sourceQuadraticB2Energy_column_partition_le F S₀ hζ rows cols w
        (fun _ _ => sourceQuadraticB2Bump_nonneg _) I index hi u
    _ ≤ I.card * ∑ j ∈ I, (A * Z) * coeffMass (block j) u :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum (hblock u)) (Nat.cast_nonneg _)
    _ = I.card * ((A * Z) * coeffMass cols u) := by rw [← Finset.mul_sum, hsum]
    _ ≤ (D₀ * T ^ δ) * ((A * Z) * coeffMass cols u) :=
      mul_le_mul_of_nonneg_right hIcard
        (mul_nonneg (mul_nonneg (zero_le_one.trans hA) hZ) (coeffMass_nonneg _ _))
    _ = _ := by dsimp [Z]; rw [← hcombine]; ring

end
end ArtinMatthews.SourceEulerAssembly
