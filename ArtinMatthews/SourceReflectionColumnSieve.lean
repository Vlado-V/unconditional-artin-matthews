module

public import ArtinMatthews.SourceReflectionExpansion
public import ArtinMatthews.SourceReflectedColumnDyad
public import ArtinMatthews.SourceReflectedColumnProfile
public import ArtinMatthews.SourceReflectedLogProfile
public import ArtinMatthews.SourceReflectionIdealCutoffs
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
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! The actual quadratic column dyad, with separate row weights and the
literal column-only retained mask. -/
namespace ArtinMatthews.SourceEulerAssembly
open NumberField IsDedekindDomain SourceReflection MeasureTheory
open scoped NumberField Classical BigOperators ContDiff
noncomputable section

variable (F : Type) [Field F] [NumberField F]
variable (S₀ : Finset (HeightOneSpectrum (𝓞 F)))
variable {ζ : F} (hζ : IsPrimitiveRoot ζ 12)
variable {U : Type} (A : SourceReflectionExpansionData F S₀ U)

local notation "Prime" => SourceExteriorPrime F S₀
local notation "E" => SourcePrimeExponents F S₀
local notation "q" => sourcePrimeExponentNorm F S₀

def sourceReflectionRowVector (rows : Finset E) (a : E → ℂ) : EuclideanSpace ℂ rows :=
  WithLp.toLp 2 (fun d : rows => a d.val)

@[simp] theorem sourceReflectionRowVector_apply (rows : Finset E) (a : E → ℂ) (d : rows) :
    sourceReflectionRowVector F S₀ rows a d = a d.val := rfl

theorem sourceReflectionRowVector_sum {ι : Type*} (rows : Finset E) (T : Finset ι)
    (a : ι → E → ℂ) :
    sourceReflectionRowVector F S₀ rows (fun d => ∑ i ∈ T, a i d) =
      ∑ i ∈ T, sourceReflectionRowVector F S₀ rows (a i) := by
  ext d
  simp

theorem sourceReflectionRowVector_mul (rows : Finset E) (z : ℂ) (a : E → ℂ) :
    sourceReflectionRowVector F S₀ rows (fun d => z * a d) =
      z • sourceReflectionRowVector F S₀ rows a := rfl

theorem sourceReflectionRowVector_norm_sq (rows : Finset E) (a : E → ℂ) :
    ‖sourceReflectionRowVector F S₀ rows a‖ ^ 2 = ∑ d ∈ rows, ‖a d‖ ^ 2 := by
  rw [PiLp.norm_sq_eq_of_L2]
  simpa only [sourceReflectionRowVector_apply] using
    (Finset.sum_coe_sort rows (fun d => ‖a d‖ ^ 2))

def sourceReflectionColumnBlock (Z R : ℝ) (h : E) (f : Finset Prime) (a n : E) (u : U)
    (cols : Finset E) (d : E) : ℂ :=
  ∑ c ∈ cols, A.row h f a n u d * sourceReflectionQuadraticSymbol F S₀ hζ d c *
    (if sourceReflectionTermLength F S₀ a n c ≤ R then
      sourceReflectionColumnCoefficient F S₀ A h f a n u c else 0) *
    A.profile h f a n u (sourceReflectionTermLength F S₀ a n c /
      sourceReflectionTermScale F S₀ Z f d)

theorem exists_sourceReflectionColumnBlock_norm_le
    (hsieve : SourceReflectionQuadraticSieve F S₀ hζ) {δ₂ : ℝ} (hδ₂ : 0 < δ₂) :
    ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ Z R D C : ℝ, 0 < Z → 1 ≤ D → 1 ≤ C →
      ∀ rows cols : Finset E,
        (∀ d ∈ rows, sourceReflectionIsSquarefree d ∧ D ≤ (q d : ℝ) ∧ (q d : ℝ) < 2 * D) →
        (∀ c ∈ cols, sourceReflectionIsSquarefree c ∧ C ≤ (q c : ℝ) ∧ (q c : ℝ) < 2 * C) →
        ∀ (h : E) (f : Finset Prime) (a n : E) (u : U),
          ‖sourceReflectionRowVector F S₀ rows
            (sourceReflectionColumnBlock F S₀ hζ A Z R h f a n u cols)‖ ≤
              C₀ * Real.sqrt (D + C) * (D * C) ^ (δ₂ / 2) := by
  obtain ⟨B, hB, hs⟩ := hsieve δ₂ hδ₂
  obtain ⟨B₁, hB₁, hb⟩ := exists_sourceReflectionDyadReciprocal_le F S₀
  obtain ⟨α, hα, hd⟩ := A.profile_derivative
  obtain ⟨M, hM, hM'⟩ := hd 1 (by norm_num)
  obtain ⟨L, hL, hfourier⟩ := sourceReflectedLogFourier_exists hα (by norm_num : (0 : ℝ) ≤ 1) hM
  let B₀ := 2 * B * (4 : ℝ) ^ δ₂
  have hB₀ : 0 < B₀ := by dsimp [B₀]; positivity
  refine ⟨1 + L * Real.sqrt B₀ * Real.sqrt B₁, by positivity, ?_⟩
  intro Z R D C hZ hD hC rows cols hrows hcols h f a n u
  have hd₀ := zero_lt_one.trans_le hD
  have hc₀ := zero_lt_one.trans_le hC
  let K (d : rows) (c : cols) := sourceReflectionQuadraticSymbol F S₀ hζ d.val c.val
  let W := Real.sqrt (B₀ * (D + C) * (D * C) ^ δ₂)
  have hW : 0 ≤ W := Real.sqrt_nonneg _
  have hK (z : cols → ℂ) : (∑ d : rows, ‖∑ c : cols, K d c * z c‖ ^ 2) ≤
      W ^ 2 * ∑ c : cols, ‖z c‖ ^ 2 := by
    have hh := hs (2 * D) (2 * C) (by linarith) (by linarith) rows cols
      (fun d hd => ⟨(hrows d hd).1, (hrows d hd).2.2.le⟩)
      (fun c hc => ⟨(hcols c hc).1, (hcols c hc).2.2.le⟩) z
    have hWsq : W ^ 2 = B * (2 * D + 2 * C) * (2 * D * (2 * C)) ^ δ₂ := by
      dsimp [W, B₀]
      rw [Real.sq_sqrt (by positivity), show 2 * D * (2 * C) = 4 * (D * C) by ring,
        Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 4) (mul_nonneg hd₀.le hc₀.le)]
      ring
    rw [hWsq]
    exact hh
  let keep (c : cols) := sourceReflectionTermLength F S₀ a n c.val ≤ R
  let b (c : cols) := sourceReflectionColumnCoefficient F S₀ A h f a n u c.val
  have hmass : (∑ c : cols, ‖if keep c then b c else 0‖ ^ 2) ≤ B₁ := by
    calc
      _ ≤ ∑ c : cols, (q c.val : ℝ)⁻¹ := by
        apply Finset.sum_le_sum
        intro c _
        by_cases hc : keep c
        · rw [ite_eq_left hc]
          exact sourceReflectionColumnCoefficient_norm_sq_le F S₀ A h f a n u c.val
        · rw [ite_eq_right hc, norm_zero, zero_pow (by decide : (2 : ℕ) ≠ 0)]
          exact inv_nonneg.mpr (Nat.cast_nonneg _)
      _ = ∑ c ∈ cols, (q c : ℝ)⁻¹ := Finset.sum_coe_sort cols (fun c : E => (q c : ℝ)⁻¹)
      _ ≤ B₁ := hb C hC cols (fun c hc => ⟨(hcols c hc).2.1, (hcols c hc).2.2.le⟩)
  let Ω := Z * (q a : ℝ) * (q n : ℝ) ^ 3 /
    (q (sourceReflectionActiveExponents F S₀ f) : ℝ) ^ 2
  have ha := zero_lt_one.trans_le (sourceReflection_norm_one_le F S₀ a)
  have hn := zero_lt_one.trans_le (sourceReflection_norm_one_le F S₀ n)
  have hf := zero_lt_one.trans_le (sourceReflection_norm_one_le F S₀ (sourceReflectionActiveExponents F S₀ f))
  have hΩ : 0 < Ω := by dsimp [Ω]; positivity
  let v₀ := Ω * C / D ^ 2
  have hv₀ : 0 < v₀ := by dsimp [v₀]; positivity
  let Φ := A.profile h f a n u
  have hΦ := A.profile_smooth h f a n u
  let g := sourceReflectedFourierCoefficient (sourceReflectedLogProfile Φ hΦ v₀)
  obtain ⟨hg, hinv, hL1⟩ := hfourier Φ hΦ (hM' h f a n u) v₀ hv₀
  have hcost : (∫ τ : ℝ, ‖g τ‖) ≤ L := hL1.trans
    ((mul_le_mul_of_nonneg_left (sourceReflectedTwoEnded_le_one hα (by norm_num) hv₀) hL).trans_eq (mul_one _))
  have hcol := source_fourier_separated_column_dyad_energy K hW hK
    (fun d : rows => A.row h f a n u d.val) (fun d => A.row_bound h f a n u d.val)
    b keep Ω hd₀ hc₀ (fun d : rows => (q d.val : ℝ)) (fun c : cols => (q c.val : ℝ))
    (fun d => (hrows d.val d.property).2) (fun c => (hcols c.val c.property).2)
    Φ g hg hinv
  have hW' : W = Real.sqrt B₀ * Real.sqrt (D + C) * (D * C) ^ (δ₂ / 2) := by
    dsimp [W]
    rw [Real.sqrt_mul (by positivity : 0 ≤ B₀ * (D + C)), Real.sqrt_mul hB₀.le,
      Real.sqrt_eq_rpow ((D * C) ^ δ₂), ← Real.rpow_mul (mul_nonneg hd₀.le hc₀.le)]
    congr 2
    ring
  have hblock (d : rows) : sourceReflectionColumnBlock F S₀ hζ A Z R h f a n u cols d.val =
      ∑ c : cols, A.row h f a n u d.val * K d c * (if keep c then b c else 0) *
        Φ (Ω * q c.val / (q d.val : ℝ) ^ 2) := by
    unfold sourceReflectionColumnBlock
    rw [← Finset.sum_coe_sort cols]
    apply Finset.sum_congr rfl
    intro c _
    rw [sourceReflectionTermLength_div_scale F S₀ hZ]
  rw [EuclideanSpace.norm_eq]
  change Real.sqrt (∑ d : rows, ‖sourceReflectionColumnBlock F S₀ hζ A Z R h f a n u cols d.val‖ ^ 2) ≤ _
  calc
    _ ≤ (∫ τ : ℝ, ‖g τ‖) * W * Real.sqrt (∑ c : cols, ‖if keep c then b c else 0‖ ^ 2) := by
      simpa only [hblock] using hcol
    _ ≤ L * W * Real.sqrt B₁ := by
      apply mul_le_mul (mul_le_mul_of_nonneg_right hcost hW) (Real.sqrt_le_sqrt hmass)
      · exact Real.sqrt_nonneg _
      · positivity
    _ = (L * Real.sqrt B₀ * Real.sqrt B₁) * Real.sqrt (D + C) * (D * C) ^ (δ₂ / 2) := by
      rw [hW']
      ring
    _ ≤ _ := by gcongr; linarith

end
end ArtinMatthews.SourceEulerAssembly
