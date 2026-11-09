module

public import ArtinMatthews.SourceSLocalOtherMellin
public import ArtinMatthews.SourceComplexMellinRapid


set_option backward.privateInPublic true
@[expose] public section

/-! The normalized chosen complex Mellin factor times the actual retained product. -/

namespace ArtinMatthews.SourcePhysical
open NumberField NumberField.InfinitePlace IsDedekindDomain MeasureTheory
open ArtinMatthews.VaryingKummerAnalytic
open scoped NumberField BigOperators Classical SchwartzMap
noncomputable section

variable {K : Type} [Field K] [NumberField K]
variable (S : Finset (HeightOneSpectrum (𝓞 K))) (v : InfinitePlace K)
variable [∀ w : InfinitePlace K, MeasurableSpace w.Completionˣ]
variable [∀ p : S, MeasurableSpace (p.val.adicCompletion K)ˣ]
variable (μarch : ∀ w : InfinitePlace K, Measure w.Completionˣ)
variable (μf : ∀ p : S, Measure (p.val.adicCompletion K)ˣ)
variable (garch : ∀ w : InfinitePlace K, w.Completionˣ → ℂ)
variable (gf : ∀ p : S, (p.val.adicCompletion K)ˣ → ℂ)

/-- A local Mellin factor with the squared complex-place norm. -/
def sourceSheetArchMellin (w : InfinitePlace K) (s : ℂ) : ℂ :=
  ∫ z, garch w z * (sourceSheetArchNorm w z : ℂ) ^ s ∂μarch w

/-- A local Mellin factor with the normalized finite-place norm. -/
def sourceSheetFiniteMellin (p : S) (s : ℂ) : ℂ :=
  ∫ z, gf p z * (sourceSheetFiniteNorm S p z : ℂ) ^ s ∂μf p

/-- The chosen complex transform times the retained tensor integral on its actual measure. -/
def sourceSLocalMellinProduct (g : 𝓢(ℂ, ℂ)) (s : ℂ) : ℂ :=
  sourceComplexMellin g s * sourceSheetOtherMellin S v μarch μf garch gf s

variable [IsTotallyComplex K]
variable [∀ w, SigmaFinite (μarch w)] [∀ p, SigmaFinite (μf p)]

theorem sourceSLocalMellinProduct_eq_prod (g : 𝓢(ℂ, ℂ)) (s : ℂ) :
    sourceSLocalMellinProduct S v μarch μf garch gf g s =
      sourceComplexMellin g s *
        ((∏ w : {w : InfinitePlace K // w ≠ v}, sourceSheetArchMellin μarch garch w.val s) *
          ∏ p : S, sourceSheetFiniteMellin S μf gf p s) := by
  rw [sourceSLocalMellinProduct, sourceSheetOtherMellin_eq_prod]
  rfl

/-- A bounded retained product preserves all orders of vertical decay. -/
theorem sourceSLocalMellinProduct_vertical_rapid (n : ℕ) (g : 𝓢(ℂ, ℂ))
    (lo hi : ℝ) (hlo : 0 < lo)
    (harch : ∀ w : {w : InfinitePlace K // w ≠ v}, ∃ A : ℝ, 0 ≤ A ∧
      ∀ s : ℂ, lo ≤ s.re → s.re ≤ hi → ‖sourceSheetArchMellin μarch garch w.val s‖ ≤ A)
    (hf : ∀ p : S, ∃ B : ℝ, 0 ≤ B ∧
      ∀ s : ℂ, lo ≤ s.re → s.re ≤ hi → ‖sourceSheetFiniteMellin S μf gf p s‖ ≤ B) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℂ, lo ≤ s.re → s.re ≤ hi →
      (1 + |s.im|) ^ n * ‖sourceSLocalMellinProduct S v μarch μf garch gf g s‖ ≤ C := by
  choose A hA using harch
  choose B hB using hf
  obtain ⟨C, hC, hg⟩ := sourceComplexMellin_vertical_rapid n g lo hi hlo
  let a : ℝ := ∏ w, A w
  let b : ℝ := ∏ p, B p
  have ha : 0 ≤ a := Finset.prod_nonneg fun w _ => (hA w).1
  have hb : 0 ≤ b := Finset.prod_nonneg fun p _ => (hB p).1
  refine ⟨C * (a * b), mul_nonneg hC (mul_nonneg ha hb), ?_⟩
  intro s hl hh
  let Aₛ (w : {w : InfinitePlace K // w ≠ v}) := ‖sourceSheetArchMellin μarch garch w.val s‖
  let Bₛ (p : S) := ‖sourceSheetFiniteMellin S μf gf p s‖
  have hAₛ : (∏ w, Aₛ w) ≤ a :=
    Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) (fun w _ => (hA w).2 s hl hh)
  have hBₛ : (∏ p, Bₛ p) ≤ b :=
    Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) (fun p _ => (hB p).2 s hl hh)
  have hBₛ0 : 0 ≤ ∏ p, Bₛ p := Finset.prod_nonneg fun _ _ => norm_nonneg _
  have hABₛ : (∏ w, Aₛ w) * (∏ p, Bₛ p) ≤ a * b :=
    mul_le_mul hAₛ hBₛ hBₛ0 ha
  rw [sourceSLocalMellinProduct_eq_prod, norm_mul, norm_mul, norm_prod, norm_prod, ← mul_assoc]
  exact mul_le_mul (hg s hl hh) hABₛ
    (mul_nonneg (Finset.prod_nonneg fun _ _ => norm_nonneg _) hBₛ0) hC

end
end ArtinMatthews.SourcePhysical
