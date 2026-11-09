module

public import ArtinMatthews.SourceQuadraticLemma51


set_option backward.privateInPublic true
@[expose] public section

/-! The same finite reduction for the squared B2 operator norm. The
small common-ideal inputs are bounds for the actual B3 blocks. -/

namespace ArtinMatthews.SourceEulerAssembly
noncomputable section
open NumberField IsDedekindDomain
open scoped NumberField Classical BigOperators

variable (F : Type) [Field F] [NumberField F]
variable (S₀ : Finset (HeightOneSpectrum (𝓞 F))) {ζ : F} (hζ : IsPrimitiveRoot ζ 12)

local notation "E" => SourcePrimeExponents F S₀
local notation "q" => sourcePrimeExponentNorm F S₀
local notation "χ" => sourceReflectionQuadraticSymbol F S₀ hζ

theorem sourceQuadratic_squarefree_mem_B2SharpRows {M K : ℝ}
    (hM : 0 < M) (hK : K ≤ M / 2) (d : E) (hs : sourceReflectionIsSquarefree d)
    (hlo : M ≤ (q d : ℝ)) (hhi : (q d : ℝ) ≤ 2 * M) :
    d ∈ sourceQuadraticB2SharpRows F S₀ M K := by
  have hp : sourceReflectionParity d = d := by
    ext P
    simp only [sourceReflectionParity, Finsupp.mapRange_apply]
    exact Nat.mod_eq_of_lt (lt_of_le_of_lt (hs P) (by decide))
  apply Finset.mem_filter.mpr
  refine ⟨(sourceReflection_mem_boundedExponents F S₀ (by positivity) d).mpr hhi, hlo, ?_⟩
  rw [hp]
  linarith

theorem sourceQuadraticSmallCommonIdeals_mono {A B : Finset E} (h : A ⊆ B) (H : ℝ) :
    sourceQuadraticSmallCommonIdeals F S₀ A H ⊆ sourceQuadraticSmallCommonIdeals F S₀ B H := by
  intro g hg
  obtain ⟨hg₁, hg₂⟩ := Finset.mem_filter.mp hg
  obtain ⟨p, hp, hpg⟩ := Finset.mem_image.mp hg₁
  obtain ⟨hp₁, hp₂⟩ := Finset.mem_product.mp hp
  exact Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨p, Finset.mem_product.mpr ⟨h hp₁, h hp₂⟩, hpg⟩, hg₂⟩

theorem sourceQuadraticB2Norm_common_reduction (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ {N H : ℝ}, 1 ≤ N → 0 < H → ∀ (rows : Finset E)
      (w : E → ℝ), (∀ d ∈ rows, 0 ≤ w d) →
      ∀ {G : Type} [Fintype G] [DecidableEq G] (label : E → G) (b3 : E → ℝ),
      let cols := sourceQuadraticB2Columns F S₀ N
      let B c := sourceQuadraticClassColumns F S₀ cols label c
      (∀ g ∈ sourceQuadraticSmallCommonIdeals F S₀ cols H, 0 ≤ b3 g) →
      (∀ c : G, ∀ g ∈ sourceQuadraticSmallCommonIdeals F S₀ (B c) H, ∀ a : E → ℂ,
        (sourceQuadraticB3Block F S₀ hζ rows (B c) w a g).re ≤
          b3 g * QuadraticScale.coeffMass (B c) a) →
      sourceQuadraticB2Norm F S₀ hζ rows w N ≤ (Fintype.card G : ℝ) *
        ((∑ g ∈ sourceQuadraticSmallCommonIdeals F S₀ cols H, b3 g) +
         C * N^ε * sourceQuadraticB2Norm F S₀ hζ rows w (N / H)) := by
  obtain ⟨C, hC, hred⟩ := sourceQuadraticB2Energy_class_common_reduction F S₀ hζ ε hε
  refine ⟨C, hC, ?_⟩
  intro N H hN hH rows w hw G _ _ label b3 cols B hb3 hB3
  let D := sourceQuadraticSmallCommonIdeals F S₀ cols H
  let S := ∑ g ∈ D, b3 g
  let tail := C * N^ε * sourceQuadraticB2Norm F S₀ hζ rows w (N / H)
  have hcols (b : E) (hb : b ∈ cols) : (q b : ℝ) ≤ N ∧ sourceReflectionIsSquarefree b :=
    (sourceQuadratic_mem_B2Columns F S₀ (zero_le_one.trans hN) b).mp hb
  have hS : 0 ≤ S := Finset.sum_nonneg hb3
  have htail : 0 ≤ tail := by
    dsimp only [tail]
    exact mul_nonneg (mul_nonneg hC.le (Real.rpow_nonneg (zero_le_one.trans hN) _))
      (sourceQuadraticB2Norm_nonneg F S₀ hζ rows w (N / H))
  have hR : 0 ≤ (Fintype.card G : ℝ) * (S + tail) :=
    mul_nonneg (Nat.cast_nonneg _) (add_nonneg hS htail)
  change ‖OAI.FiniteSieveOperator.operator (sourceQuadraticB2Matrix F S₀ hζ rows w N)‖ ^ 2 ≤
    (Fintype.card G : ℝ) * (S + tail)
  apply OAI.FiniteSieveOperator.squared_norm_le_of_energy _ _ hR
  intro a
  let v (b : E) : ℂ := if h : b ∈ cols then a ⟨b, h⟩ else 0
  have hv (b : cols) : v b.val = a b := dite_eq_left b.property
  have henergy : (∑ d : rows, ‖∑ b : cols, sourceQuadraticB2Matrix F S₀ hζ rows w N d b * a b‖ ^ 2) =
      sourceQuadraticB2Energy F S₀ hζ rows cols w v := by
    rw [sourceQuadraticB2Energy, ← Finset.sum_coe_sort rows
      (fun d => w d * ‖QuadraticScale.rowValue cols χ v d‖ ^ 2)]
    apply Finset.sum_congr rfl
    intro d _
    change ‖∑ b : cols, (Real.sqrt (w d.val) : ℂ) * χ d.val b.val * a b‖ ^ 2 =
      w d.val * ‖QuadraticScale.rowValue cols χ v d.val‖ ^ 2
    rw [sourceQuadratic_scaled_row_sq F S₀ hζ cols _ (hw d.val d.property) d.val a]
    unfold QuadraticScale.rowValue
    rw [← Finset.sum_coe_sort cols (fun b => χ d.val b * v b)]
    simp only [hv]
  have hmass : (∑ b : cols, ‖a b‖ ^ 2) = QuadraticScale.coeffMass cols v := by
    rw [QuadraticScale.coeffMass, ← Finset.sum_coe_sort cols (fun b => ‖v b‖ ^ 2)]
    simp only [hv]
  rw [henergy, hmass]
  have hsingle (c : G) :
      (∑ g ∈ sourceQuadraticSmallCommonIdeals F S₀ (B c) H,
        (sourceQuadraticB3Block F S₀ hζ rows (B c) w v g).re) ≤
        S * QuadraticScale.coeffMass (B c) v := by
    calc
      _ ≤ ∑ g ∈ sourceQuadraticSmallCommonIdeals F S₀ (B c) H,
          b3 g * QuadraticScale.coeffMass (B c) v :=
        Finset.sum_le_sum (fun g hg => hB3 c g hg v)
      _ = (∑ g ∈ sourceQuadraticSmallCommonIdeals F S₀ (B c) H, b3 g) *
          QuadraticScale.coeffMass (B c) v := (Finset.sum_mul ..).symm
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (Finset.sum_le_sum_of_subset_of_nonneg
          (sourceQuadraticSmallCommonIdeals_mono F S₀ (Finset.filter_subset _ _) H)
          (fun g hg _ => hb3 g hg)) (QuadraticScale.coeffMass_nonneg _ _)
  have hsmall : (∑ c : G, ∑ g ∈ sourceQuadraticSmallCommonIdeals F S₀ (B c) H,
      (sourceQuadraticB3Block F S₀ hζ rows (B c) w v g).re) ≤ S * QuadraticScale.coeffMass cols v := by
    calc
      _ ≤ ∑ c : G, S * QuadraticScale.coeffMass (B c) v := Finset.sum_le_sum (fun c _ => hsingle c)
      _ = _ := by rw [← Finset.mul_sum, sourceQuadratic_coeffMass_class_sum F S₀ cols label v]
  calc
    _ ≤ (Fintype.card G : ℝ) * ((∑ c : G, ∑ g ∈ sourceQuadraticSmallCommonIdeals F S₀ (B c) H,
          (sourceQuadraticB3Block F S₀ hζ rows (B c) w v g).re) +
        tail * QuadraticScale.coeffMass cols v) := hred hN hH rows cols w hw hcols v label
    _ ≤ (Fintype.card G : ℝ) * (S * QuadraticScale.coeffMass cols v +
        tail * QuadraticScale.coeffMass cols v) :=
      mul_le_mul_of_nonneg_left (add_le_add hsmall le_rfl) (Nat.cast_nonneg _)
    _ = _ := by ring

end
end ArtinMatthews.SourceEulerAssembly
