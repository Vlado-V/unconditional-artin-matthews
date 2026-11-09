module

public import ArtinMatthews.SourceQuadraticB2NormReduction
public import ArtinMatthews.SourceQuadraticSieveEnergy


set_option backward.privateInPublic true
@[expose] public section

/-! The smoothed B2 operator contains every squarefree row dyad, and
its final column ball of length one has only a bounded number of columns. -/
namespace ArtinMatthews.SourceEulerAssembly

open NumberField IsDedekindDomain VaryingKummerAnalytic QuadraticScale
open OAI.FiniteSieveOperator
open scoped NumberField Classical BigOperators

noncomputable section

variable (F : Type) [Field F] [NumberField F]
variable (S₀ : Finset (HeightOneSpectrum (𝓞 F))) {ζ : F} (hζ : IsPrimitiveRoot ζ 12)

local notation "E" => SourcePrimeExponents F S₀
local notation "SQ" => ReflectionSquarefreeExponents F S₀
local notation "q" => sourcePrimeExponentNorm F S₀
local notation "χ" => sourceReflectionQuadraticSymbol F S₀ hζ

theorem sourceQuadraticB2Bump_le_one (t : ℝ) : sourceQuadraticB2Bump t ≤ 1 :=
  OAI.QuadraticInitialBound.annularSieveBump.le_one

def sourceQuadraticB2RowWeight (M : ℝ) (d : E) : ℝ :=
  sourceQuadraticB2Bump ((q d : ℝ) / M)

abbrev sourceQuadraticSmoothedB2Norm (M K N : ℝ) : ℝ :=
  sourceQuadraticB2Norm F S₀ hζ (sourceQuadraticB2Rows F S₀ M K)
    (sourceQuadraticB2RowWeight F S₀ M) N

theorem sourceQuadraticSmoothedB2Norm_crude :
    ∃ C : ℝ, 0 < C ∧ ∀ M K N : ℝ, 1 ≤ M → 1 ≤ N →
      sourceQuadraticSmoothedB2Norm F S₀ hζ M K N ≤ C * M * N := by
  obtain ⟨C, hC, hcount⟩ := exists_sourceReflectionExteriorCard_le F S₀
  refine ⟨(5 / 2) * C ^ 2, by positivity, ?_⟩
  intro M K N hM hN
  let R := sourceQuadraticB2Rows F S₀ M K
  let C₁ := sourceQuadraticB2Columns F S₀ N
  let A := sourceQuadraticB2Matrix F S₀ hζ R (sourceQuadraticB2RowWeight F S₀ M) N
  have hr : (R.card : ℝ) ≤ C * (5 * M / 2) := by
    refine hcount _ (by linarith) R (fun d hd => ?_)
    exact ((sourceQuadratic_mem_B2Rows F S₀ (zero_le_one.trans hM) d).mp hd).1
  have hc : (C₁.card : ℝ) ≤ C * N := by
    refine hcount N hN C₁ (fun d hd => ?_)
    exact ((sourceQuadratic_mem_B2Columns F S₀ (zero_le_one.trans hN) d).mp hd).1
  have hA (i : R) (j : C₁) : ‖A i j‖ ≤ 1 := by
    let w := sourceQuadraticB2RowWeight F S₀ M i.val
    have hw : 0 ≤ Real.sqrt w := Real.sqrt_nonneg _
    change ‖(Real.sqrt w : ℂ) * χ i.val j.val‖ ≤ 1
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hw]
    calc
      _ ≤ 1 * ‖χ i.val j.val‖ := mul_le_mul_of_nonneg_right
        (Real.sqrt_le_one.mpr (sourceQuadraticB2Bump_le_one _)) (norm_nonneg _)
      _ ≤ _ := by simpa only [one_mul] using
        sourceReflectionQuadraticSymbol_norm_le_one F S₀ hζ i.val j.val
  have hcrude : ‖operator A‖ ^ 2 ≤ (R.card : ℝ) * C₁.card := by
    apply squared_norm_le_of_energy _ _ (by positivity)
    intro a
    have h := isEnergyBound_card (Finset.univ : Finset R) (Finset.univ : Finset C₁) A
      (fun i _ j _ => hA i j) a
    simpa only [finiteEnergy, rowValue, coeffMass, Finset.card_univ, Fintype.card_coe] using h
  calc
    sourceQuadraticSmoothedB2Norm F S₀ hζ M K N ≤ (R.card : ℝ) * C₁.card := hcrude
    _ ≤ (C * (5 * M / 2)) * (C * N) :=
      mul_le_mul hr hc (Nat.cast_nonneg _) (by positivity)
    _ = _ := by ring

theorem sourceQuadraticDyadicEnergy_le_smoothedB2 {M K N : ℝ}
    (hM : 0 < M) (hK : K ≤ M / 2) (hN : 0 ≤ N) :
    sourceQuadraticDyadicEnergy F S₀ hζ M N ≤ sourceQuadraticSmoothedB2Norm F S₀ hζ M K N := by
  apply sourceQuadraticDyadicEnergy_le F S₀ hζ
  refine ⟨sourceQuadraticB2Norm_nonneg F S₀ hζ _ _ _, ?_⟩
  intro rows cols hr hc a
  let R := sourceQuadraticB2Rows F S₀ M K
  let C := sourceQuadraticB2Columns F S₀ N
  let w := sourceQuadraticB2RowWeight F S₀ M
  let A := sourceQuadraticB2Matrix F S₀ hζ R w N
  have hR (r : rows) : r.val.val ∈ R := by
    have hrow := hr r.val r.property
    have hsharp := sourceQuadratic_squarefree_mem_B2SharpRows F S₀ hM hK
      r.val.val r.val.property hrow.1 hrow.2
    have hpar := (Finset.mem_filter.mp hsharp).2.2
    exact (sourceQuadratic_mem_B2Rows F S₀ hM.le _).mpr
      ⟨by linarith [hrow.2], by linarith [hrow.1], hpar⟩
  have hC (c : cols) : c.val.val ∈ C :=
    (sourceQuadratic_mem_B2Columns F S₀ hN _).mpr ⟨hc c.val c.property, c.val.property⟩
  let er (r : rows) : R := ⟨r.val.val, hR r⟩
  let ec (c : cols) : C := ⟨c.val.val, hC c⟩
  have her : Function.Injective er := by
    intro r s h
    exact Subtype.ext (Subtype.ext (congrArg (fun x : R => x.val) h))
  have hec : Function.Injective ec := by
    intro c b h
    exact Subtype.ext (Subtype.ext (congrArg (fun x : C => x.val) h))
  let sub : Matrix rows cols ℂ := fun r c => A (er r) (ec c)
  have hnorm : ‖operator sub‖ ^ 2 ≤ sourceQuadraticSmoothedB2Norm F S₀ hζ M K N :=
    pow_le_pow_left₀ (norm_nonneg _) (OAI.FiniteSieveRestriction.submatrix_norm_le er her ec hec A) 2
  have hentry (r : rows) (c : cols) :
      sub r c = reflectionExponentResidueValue F hζ S₀ c.val.val
        (sourcePrimeExponentGenerator F hζ S₀ r.val.val) ^ 3 := by
    have hw : w r.val.val = 1 := by
      have hh := hr r.val r.property
      apply sourceQuadraticB2Bump_plateau
      exact ⟨(le_div_iff₀ hM).mpr (by simpa only [one_mul] using hh.1),
        (div_le_iff₀ hM).mpr hh.2⟩
    change (Real.sqrt (w r.val.val) : ℂ) * χ r.val.val c.val.val = _
    rw [hw, Real.sqrt_one, Complex.ofReal_one, one_mul]
    exact sourceReflectionQuadraticSymbol_reciprocity F S₀ hζ r.val.val c.val.val
  have henergy : (∑ r : rows, ‖∑ c : cols, sub r c * a c.val‖ ^ 2) =
      sourceQuadraticSieveRowEnergy F S₀ hζ rows cols a := by
    unfold sourceQuadraticSieveRowEnergy
    rw [← Finset.sum_coe_sort rows (fun e => ‖∑ f ∈ cols,
      a f * reflectionExponentResidueValue F hζ S₀ f.val
        (sourcePrimeExponentGenerator F hζ S₀ e.val) ^ 3‖ ^ 2)]
    apply Finset.sum_congr rfl
    intro r _
    congr 1
    congr 1
    rw [← Finset.sum_coe_sort cols (fun f => a f * reflectionExponentResidueValue F hζ S₀ f.val
      (sourcePrimeExponentGenerator F hζ S₀ r.val.val) ^ 3)]
    apply Finset.sum_congr rfl
    intro c _
    rw [hentry r c, mul_comm]
  have h := energy_bound sub (fun c : cols => a c.val)
  rw [henergy, Finset.sum_coe_sort cols (fun c => ‖a c‖ ^ 2)] at h
  exact h.trans (mul_le_mul_of_nonneg_right hnorm (Finset.sum_nonneg (fun _ _ => sq_nonneg _)))

end
end ArtinMatthews.SourceEulerAssembly
