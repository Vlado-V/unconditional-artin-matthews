module

public import ArtinMatthews.SourceQuadraticLargeCommon
public import OAI.NumberTheory.DirichletL.QuadraticSieve.AnnularRecursion


set_option backward.privateInPublic true
@[expose] public section

/-! Goldmakher–Louvel Lemma 5.1 on the actual exterior columns, with a
smoothed B2 norm at the shortened column cutoff. The remaining small
common-ideal blocks retain their signs and their fixed class slices. -/

namespace ArtinMatthews.SourceEulerAssembly
noncomputable section
open NumberField IsDedekindDomain
open scoped NumberField Classical BigOperators ContDiff

variable (F : Type) [Field F] [NumberField F]
variable (S₀ : Finset (HeightOneSpectrum (𝓞 F))) {ζ : F} (hζ : IsPrimitiveRoot ζ 12)

local notation "E" => SourcePrimeExponents F S₀
local notation "q" => sourcePrimeExponentNorm F S₀

def sourceQuadraticSmallCommonIdeals (cols : Finset E) (H : ℝ) : Finset E :=
  (sourceQuadraticCommonIdeals F S₀ cols).filter (fun g => (q g : ℝ) ≤ H)

theorem sourceQuadratic_coeffMass_class_sum {G : Type*} [Fintype G] [DecidableEq G]
    (cols : Finset E) (label : E → G) (a : E → ℂ) :
    (∑ c : G, QuadraticScale.coeffMass (sourceQuadraticClassColumns F S₀ cols label c) a) =
      QuadraticScale.coeffMass cols a :=
  Finset.sum_fiberwise_of_maps_to (fun b (_ : b ∈ cols) => Finset.mem_univ (label b))
    (fun b => ‖a b‖ ^ 2)

theorem sourceQuadraticB2Energy_class_common_reduction (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ {N H : ℝ}, 1 ≤ N → 0 < H → ∀ (rows cols : Finset E)
      (w : E → ℝ), (∀ d ∈ rows, 0 ≤ w d) →
      (∀ b ∈ cols, (q b : ℝ) ≤ N ∧ sourceReflectionIsSquarefree b) →
      ∀ (a : E → ℂ) {G : Type} [Fintype G] [DecidableEq G] (label : E → G),
      let B c := sourceQuadraticClassColumns F S₀ cols label c
      sourceQuadraticB2Energy F S₀ hζ rows cols w a ≤ (Fintype.card G : ℝ) *
        ((∑ c : G, ∑ g ∈ sourceQuadraticSmallCommonIdeals F S₀ (B c) H,
          (sourceQuadraticB3Block F S₀ hζ rows (B c) w a g).re) +
         C * N^ε * sourceQuadraticB2Norm F S₀ hζ rows w (N / H) * QuadraticScale.coeffMass cols a) := by
  obtain ⟨C, hC, htail⟩ := sourceQuadratic_largeCommon_norm_sum F S₀ hζ ε hε
  refine ⟨C, hC, ?_⟩
  intro N H hN hH rows cols w hw hcols a G _ _ label
  let B c := sourceQuadraticClassColumns F S₀ cols label c
  let small (c : G) := sourceQuadraticSmallCommonIdeals F S₀ (B c) H
  let block (c : G) (g : E) := sourceQuadraticB3Block F S₀ hζ rows (B c) w a g
  let tail := C * N^ε * sourceQuadraticB2Norm F S₀ hζ rows w (N / H)
  have hslice (c : G) :
      sourceQuadraticB2Energy F S₀ hζ rows (B c) w a ≤
        (∑ g ∈ small c, (block c g).re) + tail * QuadraticScale.coeffMass (B c) a := by
    let D := sourceQuadraticCommonIdeals F S₀ (B c)
    let large := D.filter (fun g => H < (q g : ℝ))
    have heq : sourceQuadraticB2Energy F S₀ hζ rows (B c) w a =
        ∑ g ∈ D, (block c g).re := by
      have h := congrArg Complex.re (sourceQuadraticB2Energy_eq_common_sum F S₀ hζ rows (B c) w a)
      simpa only [Complex.ofReal_re, Complex.re_sum] using h
    have hpart : (∑ g ∈ D, (block c g).re) =
        (∑ g ∈ small c, (block c g).re) + ∑ g ∈ large, (block c g).re := by
      simpa only [small, sourceQuadraticSmallCommonIdeals, large, D, not_le] using
        (Finset.sum_filter_add_sum_filter_not D (fun g => (q g : ℝ) ≤ H)
          (fun g => (block c g).re)).symm
    rw [heq, hpart]
    apply add_le_add le_rfl
    calc
      _ ≤ ∑ g ∈ large, ‖block c g‖ := Finset.sum_le_sum (fun _ _ => Complex.re_le_norm _)
      _ ≤ _ := htail hN hH rows (B c) w hw (fun b hb => hcols b (Finset.mem_filter.mp hb).1) a
  change _ ≤ (Fintype.card G : ℝ) *
    ((∑ c : G, ∑ g ∈ small c, (block c g).re) + tail * QuadraticScale.coeffMass cols a)
  apply (sourceQuadraticB2Energy_le_class_sum F S₀ hζ rows cols w hw a label).trans
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
  calc
    _ ≤ ∑ c : G, ((∑ g ∈ small c, (block c g).re) + tail * QuadraticScale.coeffMass (B c) a) :=
      Finset.sum_le_sum (fun c _ => hslice c)
    _ = _ := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum]
      rw [sourceQuadratic_coeffMass_class_sum F S₀ cols label a]

def sourceQuadraticB2Bump (t : ℝ) : ℝ := OAI.QuadraticInitialBound.annularSieveBump (t / 2)

theorem sourceQuadraticB2Bump_smooth : ContDiff ℝ ∞ sourceQuadraticB2Bump :=
  OAI.QuadraticInitialBound.annularSieveBump.contDiff.comp (contDiff_id.div_const 2)

theorem sourceQuadraticB2Bump_nonneg (t : ℝ) : 0 ≤ sourceQuadraticB2Bump t :=
  OAI.QuadraticInitialBound.annularSieveBump.nonneg

theorem sourceQuadraticB2Bump_plateau (t : ℝ) (ht : t ∈ Set.Icc (1 : ℝ) 2) :
    sourceQuadraticB2Bump t = 1 :=
  OAI.QuadraticInitialBound.annularSieveBump_eq_one (by linarith [ht.1]) (by linarith [ht.2])

theorem sourceQuadraticB2Bump_tsupport :
    tsupport sourceQuadraticB2Bump ⊆ Set.Icc (1 / 2 : ℝ) (5 / 2) := by
  apply closure_minimal _ isClosed_Icc
  intro t ht
  have h := Function.mem_support.mp ht
  constructor
  · by_contra! hn
    exact h (OAI.QuadraticInitialBound.annularSieveBump_zero_of_le (by linarith))
  · by_contra! hn
    exact h (OAI.QuadraticInitialBound.annularSieveBump_zero_of_ge (by linarith))

theorem sourceQuadraticB2Bump_compactSupport : HasCompactSupport sourceQuadraticB2Bump :=
  isCompact_Icc.of_isClosed_subset isClosed_closure sourceQuadraticB2Bump_tsupport

theorem sourceQuadratic_lemma_5_1 (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ {M N H K : ℝ}, 0 < M → 1 ≤ N → 0 < H →
      ∀ (a : E → ℂ) {G : Type} [Fintype G] [DecidableEq G] (label : E → G),
      let rows := sourceQuadraticB2Rows F S₀ M K
      let cols := sourceQuadraticB2Columns F S₀ N
      let w (d : E) := sourceQuadraticB2Bump ((q d : ℝ) / M)
      let B c := sourceQuadraticClassColumns F S₀ cols label c
      sourceQuadraticB2Energy F S₀ hζ (sourceQuadraticB2SharpRows F S₀ M K) cols (fun _ => 1) a ≤
        (Fintype.card G : ℝ) *
          ((∑ c : G, ∑ g ∈ sourceQuadraticSmallCommonIdeals F S₀ (B c) H,
            (sourceQuadraticB3Block F S₀ hζ rows (B c) w a g).re) +
           C * N^ε * sourceQuadraticB2Norm F S₀ hζ rows w (N / H) * QuadraticScale.coeffMass cols a) := by
  obtain ⟨C, hC, h⟩ := sourceQuadraticB2Energy_class_common_reduction F S₀ hζ ε hε
  refine ⟨C, hC, ?_⟩
  intro M N H K hM hN hH a G _ _ label
  exact (sourceQuadraticB2SharpEnergy_le_smoothed F S₀ hζ M K hM sourceQuadraticB2Bump
    sourceQuadraticB2Bump_nonneg (fun t ht => (sourceQuadraticB2Bump_plateau t ht).ge) _ a).trans
      (h hN hH _ _ _ (fun _ _ => sourceQuadraticB2Bump_nonneg _)
        (fun b hb => (sourceQuadratic_mem_B2Columns F S₀ (zero_le_one.trans hN) b).mp hb) a label)

end
end ArtinMatthews.SourceEulerAssembly
