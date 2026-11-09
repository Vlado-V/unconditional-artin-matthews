module

public import ArtinMatthews.SourceQuadraticDivisorSplit
public import OAI.NumberTheory.DirichletL.QuadraticSieve.CoprimeBilinearBound
public import OAI.NumberTheory.DirichletL.CubicSieve.Operator


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews.SourceEulerAssembly
open NumberField IsDedekindDomain OAI.FiniteSieveOperator
open scoped NumberField Classical BigOperators
noncomputable section

variable (F : Type) [Field F] [NumberField F]
variable (S₀ : Finset (HeightOneSpectrum (𝓞 F))) {ζ : F} (hζ : IsPrimitiveRoot ζ 12)
local notation "E" => SourcePrimeExponents F S₀
local notation "χ" => sourceReflectionQuadraticSymbol F S₀ hζ

def sourceQuadraticDivisorCoefficientMass (cols : Finset E) (d : E) (coeffLeft : E → ℂ) : ℝ :=
  ∑ b ∈ sourceQuadraticDivisibleColumns F S₀ cols d, (2 : ℝ) ^ b.support.card * ‖coeffLeft b‖ ^ 2

theorem sourceQuadraticSplitPairSum_cauchy (rows cols : Finset E)
    (d₁ d₂ : E) (coeffLeft coeffRight : E → ℂ) :
    (∑ a ∈ rows, ‖sourceQuadraticSplitPairSum F S₀ hζ cols a d₁ d₂ coeffLeft coeffRight‖) ^ 2 ≤
      (‖operator (sourceQuadraticShortMatrix F S₀ hζ rows cols (fun _ => 1) d₁)‖ ^ 2 *
        sourceQuadraticDivisorCoefficientMass F S₀ cols d₁ coeffLeft) *
      (‖operator (sourceQuadraticShortMatrix F S₀ hζ rows cols (fun _ => 1) d₂)‖ ^ 2 *
        sourceQuadraticDivisorCoefficientMass F S₀ cols d₂ coeffRight) := by
  let L := sourceQuadraticDivisibleColumns F S₀ cols d₁
  let R := sourceQuadraticDivisibleColumns F S₀ cols d₂
  let K₁ := sourceQuadraticShortMatrix F S₀ hζ rows cols (fun _ => 1) d₁
  let K₂ := sourceQuadraticShortMatrix F S₀ hζ rows cols (fun _ => 1) d₂
  let B := cols.biUnion (fun b => b.support)
  have hL (b : L) : b.val.support ⊆ B :=
    fun _ hp => Finset.mem_biUnion.mpr ⟨b.val, (sourceQuadratic_mem_divisibleColumns F S₀ cols d₁ b.val).mp b.property |>.1, hp⟩
  have hR (b : R) : b.val.support ⊆ B :=
    fun _ hp => Finset.mem_biUnion.mpr ⟨b.val, (sourceQuadratic_mem_divisibleColumns F S₀ cols d₂ b.val).mp b.property |>.1, hp⟩
  let inner (a : rows) : ℂ :=
    ∑ b : L, ∑ c : R,
      if Disjoint b.val.support c.val.support then
        star (star (K₁ a b) * coeffLeft b.val) * (K₂ a c * coeffRight c.val) else 0
  have hsplit (a : rows) :
      sourceQuadraticSplitPairSum F S₀ hζ cols a.val d₁ d₂ coeffLeft coeffRight =
        (χ a.val d₁ * χ a.val d₂) * inner a := by
    unfold sourceQuadraticSplitPairSum
    rw [← Finset.sum_coe_sort L]
    simp only [inner, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro b _
    rw [← Finset.sum_coe_sort R
      (fun c => if Disjoint b.val.support c.support then
        star (coeffLeft b.val) * coeffRight c * χ a.val b.val * χ a.val c else 0)]
    apply Finset.sum_congr rfl
    intro c _
    by_cases hbc : Disjoint b.val.support c.val.support
    · simp only [hbc, ite_true, K₁, K₂, sourceQuadraticShortMatrix, Real.sqrt_one,
        Complex.ofReal_one, one_mul, star_mul, star_star]
      have hb := ((sourceQuadratic_mem_divisibleColumns F S₀ cols d₁ b.val).mp b.property).2
      have hc := ((sourceQuadratic_mem_divisibleColumns F S₀ cols d₂ c.val).mp c.property).2
      have hb' : χ a.val b.val = χ a.val d₁ * χ a.val (b.val - d₁) := by
        rw [← sourceQuadraticSymbol_add_right, add_tsub_cancel_of_le hb]
      have hc' : χ a.val c.val = χ a.val d₂ * χ a.val (c.val - d₂) := by
        rw [← sourceQuadraticSymbol_add_right, add_tsub_cancel_of_le hc]
      rw [hb', hc']
      ring
    · simp only [hbc, ite_false, mul_zero]
  have hsum : (∑ a ∈ rows, ‖sourceQuadraticSplitPairSum F S₀ hζ cols a d₁ d₂ coeffLeft coeffRight‖) ≤
      ∑ a : rows, ‖inner a‖ := by
    rw [← Finset.sum_coe_sort rows]
    apply Finset.sum_le_sum
    intro a _
    rw [hsplit, norm_mul]
    apply mul_le_of_le_one_left (norm_nonneg _)
    rw [norm_mul]
    calc
      _ ≤ 1 * 1 := mul_le_mul (sourceReflectionQuadraticSymbol_norm_le_one F S₀ hζ _ _)
        (sourceReflectionQuadraticSymbol_norm_le_one F S₀ hζ _ _) (norm_nonneg _) zero_le_one
      _ = 1 := one_mul 1
  have hbound := OAI.CoprimeBilinearSieve.coprime_bilinear_operator_bound
    B (fun b : L => b.val.support) (fun b : R => b.val.support) hL hR
    (fun a b => star (K₁ a b)) K₂ (fun b => coeffLeft b.val) (fun b => coeffRight b.val)
  have hconj : ‖operator (fun a b => star (K₁ a b))‖ = ‖operator K₁‖ := by
    exact OAI.SevenEighths.CubicSieve.operator_conjugate_norm K₁
  rw [hconj] at hbound
  have hmass₁ : (∑ b : L, (2 : ℝ) ^ b.val.support.card * ‖coeffLeft b.val‖ ^ 2) =
      sourceQuadraticDivisorCoefficientMass F S₀ cols d₁ coeffLeft := by
    change (∑ b : L, (2 : ℝ) ^ b.val.support.card * ‖coeffLeft b.val‖ ^ 2) =
      ∑ b ∈ L, (2 : ℝ) ^ b.support.card * ‖coeffLeft b‖ ^ 2
    exact Finset.sum_coe_sort L
      (fun b : E => (2 : ℝ) ^ b.support.card * ‖coeffLeft b‖ ^ 2)
  have hmass₂ : (∑ b : R, (2 : ℝ) ^ b.val.support.card * ‖coeffRight b.val‖ ^ 2) =
      sourceQuadraticDivisorCoefficientMass F S₀ cols d₂ coeffRight := by
    change (∑ b : R, (2 : ℝ) ^ b.val.support.card * ‖coeffRight b.val‖ ^ 2) =
      ∑ b ∈ R, (2 : ℝ) ^ b.support.card * ‖coeffRight b‖ ^ 2
    exact Finset.sum_coe_sort R
      (fun b : E => (2 : ℝ) ^ b.support.card * ‖coeffRight b‖ ^ 2)
  rw [hmass₁, hmass₂] at hbound
  exact (pow_le_pow_left₀ (Finset.sum_nonneg (fun _ _ => norm_nonneg _)) hsum 2).trans hbound

end
end ArtinMatthews.SourceEulerAssembly
