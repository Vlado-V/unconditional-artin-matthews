module

public import ArtinMatthews.SourceReflectionRetainedFinite


set_option backward.privateInPublic true
@[expose] public section

/-! Sum the actual retained column dyads in the row Euclidean norm. -/
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

theorem exists_sourceReflectionColumnSum_norm_le
    (hsieve : SourceReflectionQuadraticSieve F S₀ hζ) {δ₂ : ℝ} (hδ₂ : 0 < δ₂) :
    ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ Z R D : ℝ, 0 < Z → 1 ≤ R → 1 ≤ D →
      ∀ rows : Finset E,
        (∀ d ∈ rows, sourceReflectionIsSquarefree d ∧ D ≤ (q d : ℝ) ∧ (q d : ℝ) < 2 * D) →
        ∀ (h : E) (f : Finset Prime) (a n : E) (u : U),
          ‖sourceReflectionRowVector F S₀ rows
            (sourceReflectionColumnBlock F S₀ hζ A Z R h f a n u
              (sourceReflectionRetainedColumns F S₀ R))‖ ≤
              C₀ * Real.log (2 * R) * Real.sqrt (D + R) * (D * R) ^ (δ₂ / 2) := by
  obtain ⟨C, hC, hc⟩ := exists_sourceReflectionColumnBlock_norm_le F S₀ hζ A hsieve hδ₂
  have hlog : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  refine ⟨C / Real.log 2, div_pos hC hlog, ?_⟩
  intro Z R D hZ hR hD rows hrows h f a n u
  let cols (j : ℕ) := sourceReflectionRetainedColumnDyad F S₀ R j
  let T := Finset.range (sourceReflectionDyadLength R)
  have hr := zero_lt_one.trans_le hR
  have hd := zero_lt_one.trans_le hD
  let B := C * Real.sqrt (D + R) * (D * R) ^ (δ₂ / 2)
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hterm (j : ℕ) :
      ‖sourceReflectionRowVector F S₀ rows
        (sourceReflectionColumnBlock F S₀ hζ A Z R h f a n u (cols j))‖ ≤ B := by
    let L := (2 : ℝ) ^ j
    have hL : 1 ≤ L := one_le_pow₀ (by norm_num)
    have hj (c : E) (hc : c ∈ cols j) :
        sourceReflectionIsSquarefree c ∧ L ≤ (q c : ℝ) ∧ (q c : ℝ) < 2 * L := by
      obtain ⟨hm, he⟩ := Finset.mem_filter.mp hc
      have hb := sourceReflectionDyad_bounds (sourcePrimeExponentNorm_pos F S₀ c)
      rw [he] at hb
      exact ⟨(Finset.mem_filter.mp hm).2, hb⟩
    by_cases hn : (cols j).Nonempty
    · obtain ⟨c, hc'⟩ := hn
      have hcR := (sourceReflection_mem_boundedExponents F S₀ hr.le c).mp
        (Finset.mem_filter.mp (Finset.mem_filter.mp hc').1).1
      have hLR := (hj c hc').2.1.trans hcR
      refine (hc Z R D L hZ hD hL rows (cols j) hrows hj h f a n u).trans ?_
      dsimp [B]
      gcongr
    · rw [Finset.not_nonempty_iff_eq_empty.mp hn]
      have hzv : sourceReflectionRowVector F S₀ rows
          (sourceReflectionColumnBlock F S₀ hζ A Z R h f a n u ∅) = 0 := by
        ext d
        simp [sourceReflectionColumnBlock]
      rwa [hzv, norm_zero]
  have he (d : E) :=
    sourceReflectionColumnBlock_sum_dyads F S₀ hζ A Z hR h f a n u d
  calc
    _ = ‖∑ j ∈ T, sourceReflectionRowVector F S₀ rows
      (sourceReflectionColumnBlock F S₀ hζ A Z R h f a n u (cols j))‖ := by
      rw [← sourceReflectionRowVector_sum]
      congr 2
      funext d
      exact he d
    _ ≤ ∑ _j ∈ T, B := norm_sum_le_of_le _ (fun j _ => hterm j)
    _ = (sourceReflectionDyadLength R : ℝ) * B := by
      simp only [Finset.sum_const, nsmul_eq_mul, Finset.card_range, T]
    _ ≤ (Real.log (2 * R) / Real.log 2) * B :=
      mul_le_mul_of_nonneg_right (sourceReflectionDyadLength_le_log hR) hB
    _ = _ := by dsimp [B]; ring

end
end ArtinMatthews.SourceEulerAssembly
