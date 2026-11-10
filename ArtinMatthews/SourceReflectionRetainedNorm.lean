module

public import ArtinMatthews.SourceReflectionColumnSieve
public import ArtinMatthews.SourceReflectionSeries
public import ArtinMatthews.SourceReflectionActiveBudget
public import ArtinMatthews.SourceReflectionColumnSum
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! Row Euclidean bounds for the retained series. The two logarithms
come from the column dyads and the harmonic cube-ideal sum. -/
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

theorem exists_sourceReflectionRetainedBranch_norm_le
    (hsieve : SourceReflectionQuadraticSieve F S₀ hζ) {δ₂ : ℝ} (hδ₂ : 0 < δ₂) :
    ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ Z R D : ℝ, 0 < Z → 1 ≤ R → 1 ≤ D →
      ∀ rows : Finset E,
        (∀ d ∈ rows, sourceReflectionIsSquarefree d ∧ D ≤ (q d : ℝ) ∧ (q d : ℝ) < 2 * D) →
        ∀ (h : E) (f : Finset Prime) (u : U),
          ‖sourceReflectionRowVector F S₀ rows
            (fun d => sourceReflectionSelectedBranch F S₀ hζ A Z h d f u (fun Q => Q ≤ R))‖ ≤
              C₀ * sourceReflectionFrozenFactors F S₀ f 0 * (Real.log (2 * R)) ^ 2 *
                Real.sqrt (D + R) * (D * R) ^ (δ₂ / 2) := by
  obtain ⟨C, hC, hc⟩ := exists_sourceReflectionColumnSum_norm_le F S₀ hζ A hsieve hδ₂
  obtain ⟨H, hH, hH'⟩ := exists_sourceReflectionHarmonic_le F S₀
  refine ⟨C * H, mul_pos hC hH, ?_⟩
  intro Z R D hZ hR hD rows hrows h f u
  let T := sourceReflectionRetainedNumerators F S₀ f R
  let N := sourceReflectionRetainedCubes F S₀ R
  let cols := sourceReflectionRetainedColumns F S₀ R
  let L := C * Real.log (2 * R) * Real.sqrt (D + R) * (D * R) ^ (δ₂ / 2)
  have hr := zero_lt_one.trans_le hR
  have hlog : 0 ≤ Real.log (2 * R) := Real.log_nonneg (by linarith)
  have hL : 0 ≤ L := by dsimp [L]; positivity
  have hnorm (a : SourceReflectionFrozenNumerator F S₀ f) (n : E) :
      ‖sourceReflectionRowVector F S₀ rows (fun d => (A.scalar h f a.val n u / (q n : ℂ)) *
        sourceReflectionColumnBlock F S₀ hζ A Z R h f a.val n u cols d)‖ ≤
        sourceReflectionFrozenWeight F S₀ f a.val * (q n : ℝ)⁻¹ * L := by
    have hs : ‖A.scalar h f a.val n u / (q n : ℂ)‖ ≤
        sourceReflectionFrozenWeight F S₀ f a.val * (q n : ℝ)⁻¹ := by
      rw [norm_div, Complex.norm_natCast, ← div_eq_mul_inv]
      exact div_le_div_of_nonneg_right (A.scalar_bound h f a.val n u) (Nat.cast_nonneg _)
    have hb := hc Z R D hZ hR hD rows hrows h f a.val n u
    rw [sourceReflectionRowVector_mul, norm_smul]
    apply mul_le_mul hs hb (norm_nonneg _)
    exact mul_nonneg (sourceReflectionFrozenWeight_nonneg F S₀ f _) (inv_nonneg.mpr (Nat.cast_nonneg _))
  have hn : ∑ n ∈ N, (q n : ℝ)⁻¹ ≤ H * Real.log (2 * R) := by
    let Y := R ^ (1 / 3 : ℝ)
    have hY : 1 ≤ Y := Real.one_le_rpow hR (by norm_num)
    have hYR : Y ≤ R := by
      simpa only [Real.rpow_one, Y] using
        Real.rpow_le_rpow_of_exponent_le hR (by norm_num : (1 / 3 : ℝ) ≤ 1)
    have hb := hH' Y hY N (fun n hn => (sourceReflection_mem_boundedExponents F S₀
      (zero_le_one.trans hY) n).mp hn)
    have hl := Real.log_le_log (by positivity : 0 < 2 * Y)
      (mul_le_mul_of_nonneg_left hYR (by norm_num))
    exact hb.trans (mul_le_mul_of_nonneg_left hl hH.le)
  have hβ : ∑ a ∈ T, sourceReflectionFrozenWeight F S₀ f a.val ≤ sourceReflectionFrozenFactors F S₀ f 0 := by
    have hd := sourceReflectionFrozenDirichlet F S₀ f (σ := 0) le_rfl
    have hs : HasSum (fun a : SourceReflectionFrozenNumerator F S₀ f =>
        sourceReflectionFrozenWeight F S₀ f a.val) (sourceReflectionFrozenFactors F S₀ f 0) := by
      simpa only [neg_zero, Real.rpow_zero, mul_one] using hd
    exact (hs.summable.sum_le_tsum T (fun a _ => sourceReflectionFrozenWeight_nonneg F S₀ f _)).trans_eq
      hs.tsum_eq
  have hvec : sourceReflectionRowVector F S₀ rows
      (fun d => sourceReflectionSelectedBranch F S₀ hζ A Z h d f u (fun Q => Q ≤ R)) =
      ∑ a ∈ T, ∑ n ∈ N, sourceReflectionRowVector F S₀ rows
        (fun d => (A.scalar h f a.val n u / (q n : ℂ)) *
          sourceReflectionColumnBlock F S₀ hζ A Z R h f a.val n u cols d) := by
    simp_rw [sourceReflectionRetainedBranch_eq_sum F S₀ hζ A Z h _ f u hR,
      sourceReflectionRowVector_sum]
    rfl
  rw [hvec]
  calc
    _ ≤ ∑ a ∈ T, ∑ n ∈ N, sourceReflectionFrozenWeight F S₀ f a.val * (q n : ℝ)⁻¹ * L := by
      apply norm_sum_le_of_le
      intro a _
      exact norm_sum_le_of_le _ (fun n _ => hnorm a n)
    _ = ∑ a ∈ T, sourceReflectionFrozenWeight F S₀ f a.val * (∑ n ∈ N, (q n : ℝ)⁻¹) * L := by
      apply Finset.sum_congr rfl
      intro a _
      rw [Finset.mul_sum, Finset.sum_mul]
    _ = (∑ a ∈ T, sourceReflectionFrozenWeight F S₀ f a.val) * (∑ n ∈ N, (q n : ℝ)⁻¹) * L := by
      rw [← Finset.sum_mul, ← Finset.sum_mul]
    _ ≤ sourceReflectionFrozenFactors F S₀ f 0 * (H * Real.log (2 * R)) * L := by
      have hN : 0 ≤ ∑ n ∈ N, (q n : ℝ)⁻¹ :=
        Finset.sum_nonneg (fun _ _ => inv_nonneg.mpr (Nat.cast_nonneg _))
      exact mul_le_mul_of_nonneg_right (mul_le_mul hβ hn hN
        (sourceReflectionFrozenFactors_nonneg F S₀ f le_rfl)) hL
    _ = _ := by dsimp [L]; ring

variable [Fintype U]

theorem exists_sourceReflectionRetainedRow_norm_le
    (hsieve : SourceReflectionQuadraticSieve F S₀ hζ) {δ₁ δ₂ : ℝ}
    (hδ₁ : 0 < δ₁) (hδ₂ : 0 < δ₂) :
    ∃ C : ℝ, 0 < C ∧ ∀ Z R P D : ℝ, 0 < Z → 1 ≤ R → 1 ≤ P → 1 ≤ D →
      ∀ rows : Finset E,
        (∀ d ∈ rows, sourceReflectionIsSquarefree d ∧ D ≤ (q d : ℝ) ∧ (q d : ℝ) < 2 * D) →
        ∀ h : E, (q h : ℝ) ≤ 2 * P →
          ‖sourceReflectionRowVector F S₀ rows
            (fun d => sourceReflectionSelectedRow F S₀ hζ A Z h d (fun Q => Q ≤ R))‖ ≤
              C * P ^ δ₁ * (Real.log (2 * R)) ^ 2 * Real.sqrt (D + R) * (D * R) ^ (δ₂ / 2) := by
  obtain ⟨C, hC, hc⟩ := exists_sourceReflectionRetainedBranch_norm_le F S₀ hζ A hsieve hδ₂
  obtain ⟨B, hB, hb⟩ := exists_sourceReflectionActiveBudget F S₀ hδ₁
  let N : ℝ := Fintype.card U
  have hN : 0 ≤ N := Nat.cast_nonneg _
  let C₀ := N * C * B * (2 : ℝ) ^ δ₁
  have hC₀ : 0 ≤ C₀ := by dsimp [C₀]; positivity
  refine ⟨1 + C₀, by linarith, ?_⟩
  intro Z R P D hZ hR hP hD rows hrows h hh
  let L := (Real.log (2 * R)) ^ 2 * Real.sqrt (D + R) * (D * R) ^ (δ₂ / 2)
  have hL : 0 ≤ L := by dsimp [L]; positivity
  have hq : (q h : ℝ) ^ δ₁ ≤ (2 : ℝ) ^ δ₁ * P ^ δ₁ := by
    rw [← Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) (zero_le_one.trans hP)]
    exact Real.rpow_le_rpow (Nat.cast_nonneg _) hh hδ₁.le
  unfold sourceReflectionSelectedRow
  simp only [sourceReflectionRowVector_sum]
  calc
    _ ≤ ∑ f ∈ sourceReflectionActiveChoices F S₀ h,
        ∑ _u : U, C * sourceReflectionFrozenFactors F S₀ f 0 * L := by
      apply norm_sum_le_of_le
      intro f _
      apply norm_sum_le_of_le
      intro u _
      exact (hc Z R D hZ hR hD rows hrows h f u).trans_eq (by dsimp [L]; ring)
    _ = N * C * L * ∑ f ∈ sourceReflectionActiveChoices F S₀ h, sourceReflectionFrozenFactors F S₀ f 0 := by
      simp only [Finset.sum_const, nsmul_eq_mul, Finset.card_univ, N, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro f _
      ring
    _ ≤ N * C * L * (B * (q h : ℝ) ^ δ₁) := mul_le_mul_of_nonneg_left (hb h 0 le_rfl) (by positivity)
    _ ≤ N * C * L * (B * ((2 : ℝ) ^ δ₁ * P ^ δ₁)) := by
      gcongr
    _ = C₀ * P ^ δ₁ * L := by dsimp [C₀]; ring
    _ ≤ _ := by
      have hn : C₀ * P ^ δ₁ * L ≤ (1 + C₀) * P ^ δ₁ * L := by gcongr; linarith
      exact hn.trans_eq (by dsimp [L]; ring)

end
end ArtinMatthews.SourceEulerAssembly
