module

public import ArtinMatthews.SourceSLocalSheetComplex
public import ArtinMatthews.SourceSLocalSheetNorm
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex


set_option backward.privateInPublic true
@[expose] public section

/-! The literal tensor on the retained S-local coordinates, with the
squared archimedean norms and the normalized finite-place norms. -/

namespace ArtinMatthews.SourcePhysical
open NumberField NumberField.InfinitePlace NumberField.InfinitePlace.Completion IsDedekindDomain
open scoped NumberField BigOperators Classical
noncomputable section

variable {K : Type} [Field K]

/-- The normalized norm at a complex archimedean unit. -/
def sourceSheetArchNorm (w : InfinitePlace K) (z : w.Completionˣ) : ℝ :=
  ‖(z : w.Completion)‖ ^ 2

theorem sourceSheetArchNorm_pos (w : InfinitePlace K) (z : w.Completionˣ) :
    0 < sourceSheetArchNorm w z := pow_pos (norm_pos_iff.mpr z.ne_zero) _

theorem sourceSheetArchNorm_eq_complex {w : InfinitePlace K} (hw : IsComplex w)
    (z : w.Completionˣ) :
    sourceSheetArchNorm w z = ‖ringEquivComplexOfIsComplex hw (z : w.Completion)‖ ^ 2 := by
  rw [sourceSheetArchNorm, sourceSheetComplex_norm hw]

variable [NumberField K]
variable (S : Finset (HeightOneSpectrum (𝓞 K))) (v : InfinitePlace K)

/-- The completion norm at a finite S-local unit. -/
def sourceSheetFiniteNorm (p : S) (z : (p.val.adicCompletion K)ˣ) : ℝ :=
  ‖(z : p.val.adicCompletion K)‖

theorem sourceSheetFiniteNorm_pos (p : S) (z : (p.val.adicCompletion K)ˣ) :
    0 < sourceSheetFiniteNorm S p z := norm_pos_iff.mpr z.ne_zero

/-- The tensor of the actual retained archimedean and finite profiles. -/
def sourceSheetOtherTensor
    (garch : ∀ w : InfinitePlace K, w.Completionˣ → ℂ)
    (gf : ∀ p : S, (p.val.adicCompletion K)ˣ → ℂ)
    (y : SNormOneOtherUnits S v) : ℂ :=
  (∏ w : {w : InfinitePlace K // w ≠ v}, garch w.val (y.1 w)) * ∏ p : S, gf p (y.2 p)

variable [IsTotallyComplex K]

theorem sourceSheetOtherNorm_eq_prod_totallyComplex (y : SNormOneOtherUnits S v) :
    sourceSheetOtherNorm S v y =
      (∏ w : {w : InfinitePlace K // w ≠ v}, sourceSheetArchNorm w.val (y.1 w)) *
        ∏ p : S, sourceSheetFiniteNorm S p (y.2 p) := by
  unfold sourceSheetOtherNorm
  congr 1
  apply Finset.prod_congr rfl
  intro w _
  rw [(IsTotallyComplex.isComplex w.val).mult_eq_two, sourceSheetArchNorm]

theorem sourceSheetOtherNorm_rpow_eq_prod (σ : ℝ) (y : SNormOneOtherUnits S v) :
    sourceSheetOtherNorm S v y ^ σ =
      (∏ w : {w : InfinitePlace K // w ≠ v}, sourceSheetArchNorm w.val (y.1 w) ^ σ) *
        ∏ p : S, sourceSheetFiniteNorm S p (y.2 p) ^ σ := by
  let A (w : {w : InfinitePlace K // w ≠ v}) := sourceSheetArchNorm w.val (y.1 w)
  let B (p : S) := sourceSheetFiniteNorm S p (y.2 p)
  have hA (w : {w : InfinitePlace K // w ≠ v}) : 0 ≤ A w :=
    (sourceSheetArchNorm_pos w.val (y.1 w)).le
  have hB (p : S) : 0 ≤ B p := (sourceSheetFiniteNorm_pos S p (y.2 p)).le
  rw [sourceSheetOtherNorm_eq_prod_totallyComplex]
  change ((∏ w,A w) * (∏ p,B p)) ^ σ = _
  rw [Real.mul_rpow (Finset.prod_nonneg fun w _ => hA w) (Finset.prod_nonneg fun p _ => hB p),
    ← Real.finsetProd_rpow Finset.univ A (fun w _ => hA w) σ,
    ← Real.finsetProd_rpow Finset.univ B (fun p _ => hB p) σ]

private theorem realFinsetProd_cpow {ι : Type*} (F : Finset ι) (a : ι → ℝ) (s : ℂ) :
    (∀ i ∈ F, 0 ≤ a i) →
      ((∏ i ∈ F, a i : ℝ) : ℂ) ^ s = ∏ i ∈ F, (a i : ℂ) ^ s := by
  induction F using Finset.induction_on with
  | empty => intro _; simp
  | insert i F hi ih =>
    intro h
    have hF (j : ι) (hj : j ∈ F) : 0 ≤ a j := h j (Finset.mem_insert_of_mem hj)
    rw [Finset.prod_insert hi, Finset.prod_insert hi, Complex.ofReal_mul,
      Complex.mul_cpow_ofReal_nonneg (h i (Finset.mem_insert_self _ _))
        (Finset.prod_nonneg hF), ih hF]

theorem sourceSheetOtherNorm_cpow_eq_prod (s : ℂ) (y : SNormOneOtherUnits S v) :
    (sourceSheetOtherNorm S v y : ℂ) ^ s =
      (∏ w : {w : InfinitePlace K // w ≠ v}, (sourceSheetArchNorm w.val (y.1 w) : ℂ) ^ s) *
        ∏ p : S, (sourceSheetFiniteNorm S p (y.2 p) : ℂ) ^ s := by
  let A (w : {w : InfinitePlace K // w ≠ v}) := sourceSheetArchNorm w.val (y.1 w)
  let B (p : S) := sourceSheetFiniteNorm S p (y.2 p)
  have hA (w : {w : InfinitePlace K // w ≠ v}) : 0 ≤ A w :=
    (sourceSheetArchNorm_pos w.val (y.1 w)).le
  have hB (p : S) : 0 ≤ B p := (sourceSheetFiniteNorm_pos S p (y.2 p)).le
  rw [sourceSheetOtherNorm_eq_prod_totallyComplex]
  change (((∏ w,A w) * (∏ p,B p) : ℝ) : ℂ) ^ s = _
  rw [Complex.ofReal_mul,
    Complex.mul_cpow_ofReal_nonneg (Finset.prod_nonneg fun w _ => hA w) (Finset.prod_nonneg fun p _ => hB p),
    realFinsetProd_cpow Finset.univ A s (fun w _ => hA w),
    realFinsetProd_cpow Finset.univ B s (fun p _ => hB p)]

variable (garch : ∀ w : InfinitePlace K, w.Completionˣ → ℂ)
variable (gf : ∀ p : S, (p.val.adicCompletion K)ˣ → ℂ)

theorem sourceSheetOtherTensor_weighted_norm_eq_prod (σ : ℝ) (y : SNormOneOtherUnits S v) :
    ‖sourceSheetOtherTensor S v garch gf y‖ * sourceSheetOtherNorm S v y ^ σ =
      (∏ w : {w : InfinitePlace K // w ≠ v},
        ‖garch w.val (y.1 w)‖ * sourceSheetArchNorm w.val (y.1 w) ^ σ) *
        ∏ p : S, ‖gf p (y.2 p)‖ * sourceSheetFiniteNorm S p (y.2 p) ^ σ := by
  simp only [sourceSheetOtherTensor, norm_mul, norm_prod,
    sourceSheetOtherNorm_rpow_eq_prod, Finset.prod_mul_distrib]
  ac_rfl

def sourceSheetOtherMellinIntegrand (s : ℂ) (y : SNormOneOtherUnits S v) : ℂ :=
  sourceSheetOtherTensor S v garch gf y * (sourceSheetOtherNorm S v y : ℂ) ^ s

theorem sourceSheetOtherMellinIntegrand_eq_prod (s : ℂ) (y : SNormOneOtherUnits S v) :
    sourceSheetOtherMellinIntegrand S v garch gf s y =
      (∏ w : {w : InfinitePlace K // w ≠ v},
        garch w.val (y.1 w) * (sourceSheetArchNorm w.val (y.1 w) : ℂ) ^ s) *
        ∏ p : S, gf p (y.2 p) * (sourceSheetFiniteNorm S p (y.2 p) : ℂ) ^ s := by
  simp only [sourceSheetOtherMellinIntegrand, sourceSheetOtherTensor,
    sourceSheetOtherNorm_cpow_eq_prod, Finset.prod_mul_distrib]
  ac_rfl

omit [IsTotallyComplex K] in
theorem sourceSheetOtherMellinIntegrand_norm (s : ℂ) (y : SNormOneOtherUnits S v) :
    ‖sourceSheetOtherMellinIntegrand S v garch gf s y‖ =
      ‖sourceSheetOtherTensor S v garch gf y‖ * sourceSheetOtherNorm S v y ^ s.re := by
  rw [sourceSheetOtherMellinIntegrand, norm_mul,
    Complex.norm_cpow_eq_rpow_re_of_pos (sourceSheetOtherNorm_pos S v y)]

end
end ArtinMatthews.SourcePhysical
