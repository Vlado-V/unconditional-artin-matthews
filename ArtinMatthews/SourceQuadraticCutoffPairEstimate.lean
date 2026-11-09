module

public import ArtinMatthews.SourceQuadraticSwappedSieve
public import ArtinMatthews.SourceQuadraticCommonIdeal
public import OAI.NumberTheory.DirichletL.QuadraticSieve.CoprimeBilinearBound


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews.SourceEulerAssembly
open NumberField IsDedekindDomain StandardAdelic OAI.FiniteSieveOperator
open scoped NumberField Classical BigOperators
noncomputable section

variable (F : Type) [Field F] [NumberField F]
variable (S₀ : Finset (HeightOneSpectrum (𝓞 F))) {ζ : F} (hζ : IsPrimitiveRoot ζ 12)
local notation "E" => SourcePrimeExponents F S₀
local notation "q" => sourcePrimeExponentNorm F S₀
local notation "χ" => sourceReflectionQuadraticSymbol F S₀ hζ

/-- The literal quadratic Gram sum with the disjoint-prime-support mask retained. -/
def sourceQuadraticCutoffPairValue (cols : Finset E) (h : E) (coeff : E → ℂ) : ℂ :=
  ∑ b ∈ cols, ∑ c ∈ cols, if Disjoint b.support c.support then
    star (χ h b * coeff b) * (χ h c * coeff c) else 0

/-- Finite coprime bilinear Cauchy applied to the actual source character matrix. -/
theorem sourceQuadraticCutoffPair_l1_le (rows cols : Finset E) (coeff : E → ℂ) :
    (∑ h ∈ rows, ‖sourceQuadraticCutoffPairValue F S₀ hζ cols h coeff‖) ≤
      ‖operator (fun (h : rows) (b : cols) => χ h.val b.val)‖ ^ 2 *
        ∑ b ∈ cols, (2 : ℝ) ^ b.support.card * ‖coeff b‖ ^ 2 := by
  let A : Matrix rows cols ℂ := fun h b => χ h.val b.val
  let B := cols.biUnion (fun b => b.support)
  have hB (b : cols) : b.val.support ⊆ B :=
    fun P hP => Finset.mem_biUnion.mpr ⟨b.val, b.property, hP⟩
  have hpair (h : rows) : sourceQuadraticCutoffPairValue F S₀ hζ cols h.val coeff =
      ∑ b : cols, ∑ c : cols, if Disjoint b.val.support c.val.support then
        star (A h b * coeff b.val) * (A h c * coeff c.val) else 0 := by
    unfold sourceQuadraticCutoffPairValue
    rw [← Finset.sum_coe_sort cols]
    apply Finset.sum_congr rfl
    intro b _
    exact (Finset.sum_coe_sort cols
      (fun c => if Disjoint b.val.support c.support then
        star (A h b * coeff b.val) * (χ h.val c * coeff c) else 0)).symm
  have hmass : (∑ b : cols, (2 : ℝ) ^ b.val.support.card * ‖coeff b.val‖ ^ 2) =
      ∑ b ∈ cols, (2 : ℝ) ^ b.support.card * ‖coeff b‖ ^ 2 :=
    Finset.sum_coe_sort cols (fun b : E => (2 : ℝ) ^ b.support.card * ‖coeff b‖ ^ 2)
  have hbound := OAI.CoprimeBilinearSieve.coprime_bilinear_operator_bound B
    (fun b : cols => b.val.support) (fun c : cols => c.val.support) hB hB A A
    (fun b => coeff b.val) (fun c => coeff c.val)
  simp_rw [← hpair] at hbound
  rw [Finset.sum_coe_sort rows (fun h : E =>
    ‖sourceQuadraticCutoffPairValue F S₀ hζ cols h coeff‖), hmass] at hbound
  have hnonneg : 0 ≤ ‖operator A‖ ^ 2 *
      ∑ b ∈ cols, (2 : ℝ) ^ b.support.card * ‖coeff b‖ ^ 2 := by positivity
  apply (sq_le_sq₀ (Finset.sum_nonneg (fun _ _ => norm_nonneg _)) hnonneg).1
  simpa only [pow_two] using hbound

private theorem support_mass_bound (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ P : ℝ, 1 ≤ P → ∀ cols : Finset E,
      (∀ b ∈ cols, (q b : ℝ) ≤ P) → ∀ coeff : E → ℂ,
      (∑ b ∈ cols, (2 : ℝ) ^ b.support.card * ‖coeff b‖ ^ 2) ≤
        C * P ^ ε * ∑ b ∈ cols, ‖coeff b‖ ^ 2 := by
  obtain ⟨C, hC, hbound⟩ := sourceQuadraticSquarefreeDivisors_small_power F S₀ ε hε
  refine ⟨C, hC, fun P _ cols hcols coeff => ?_⟩
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro b hb
  apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
  have hc := hbound b
  rw [sourceQuadraticSquarefreeDivisors_card, Nat.cast_pow, Nat.cast_ofNat] at hc
  exact hc.trans (mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow (Nat.cast_nonneg _) (hcols b hb) hε.le) hC.le)

variable [IsTotallyComplex F]

/-- The reciprocal sieve estimate controls the disjoint source pair sum over a squarefree ball. -/
theorem sourceQuadraticCutoffPair_of_exponent {α : ℝ}
    (htrace : traceBadPlaces F ⊆ sourceHilbertSet F S₀)
    (hE : QuadraticHeckeSieveExponentBound (sourceQuadraticDyadicEnergy F S₀ hζ) α)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ H P : ℝ, 1 ≤ H → 1 ≤ P → ∀ rows cols : Finset E,
      (∀ h ∈ rows, sourceReflectionIsSquarefree h ∧ (q h : ℝ) ≤ H) →
      (∀ b ∈ cols, sourceReflectionIsSquarefree b ∧ (q b : ℝ) ≤ P) →
      ∀ coeff : E → ℂ,
      (∑ h ∈ rows, ‖sourceQuadraticCutoffPairValue F S₀ hζ cols h coeff‖) ≤
        C * (H * P) ^ ε * (P + H ^ α) * ∑ b ∈ cols, ‖coeff b‖ ^ 2 := by
  obtain ⟨Cs, hCs, hs⟩ := sourceQuadratic_swapped_norm_bound F S₀ hζ htrace hE
    (ε / 2) (half_pos hε)
  obtain ⟨Cm, hCm, hm⟩ := support_mass_bound F S₀ (ε / 2) (half_pos hε)
  refine ⟨Cs * Cm, mul_pos hCs hCm, ?_⟩
  intro H P hH hP rows cols hrows hcols coeff
  have hH0 := zero_lt_one.trans_le hH
  have hP0 := zero_lt_one.trans_le hP
  have hHP0 := mul_pos hH0 hP0
  have hnorm := hs H P (by linarith) (by linarith) rows cols
    (fun h hh => ⟨(hrows h hh).1, (hrows h hh).2.trans (by linarith)⟩)
    (fun b hb => ⟨(hcols b hb).1, (hcols b hb).2.trans (by linarith)⟩)
  have hmass := hm P hP cols (fun b hb => (hcols b hb).2) coeff
  have hpow : P ^ (ε / 2) ≤ (H * P) ^ (ε / 2) :=
    Real.rpow_le_rpow hP0.le (le_mul_of_one_le_left hP0.le hH) (half_pos hε).le
  have hpows : (H * P) ^ (ε / 2) * (H * P) ^ (ε / 2) = (H * P) ^ ε := by
    rw [← Real.rpow_add hHP0, add_halves]
  calc
    _ ≤ ‖operator (fun (h : rows) (b : cols) => χ h.val b.val)‖ ^ 2 *
        ∑ b ∈ cols, (2 : ℝ) ^ b.support.card * ‖coeff b‖ ^ 2 :=
      sourceQuadraticCutoffPair_l1_le F S₀ hζ rows cols coeff
    _ ≤ (Cs * (H * P) ^ (ε / 2) * (P + H ^ α)) *
        (Cm * P ^ (ε / 2) * ∑ b ∈ cols, ‖coeff b‖ ^ 2) := by
      exact mul_le_mul hnorm hmass
        (Finset.sum_nonneg (fun _ _ => by positivity)) (by positivity)
    _ ≤ (Cs * (H * P) ^ (ε / 2) * (P + H ^ α)) *
        (Cm * (H * P) ^ (ε / 2) * ∑ b ∈ cols, ‖coeff b‖ ^ 2) := by
      gcongr
    _ = _ := by
      calc
        _ = (Cs * Cm) * ((H * P) ^ (ε / 2) * (H * P) ^ (ε / 2)) *
            (P + H ^ α) * ∑ b ∈ cols, ‖coeff b‖ ^ 2 := by ring
        _ = _ := by rw [hpows]

end
end ArtinMatthews.SourceEulerAssembly
