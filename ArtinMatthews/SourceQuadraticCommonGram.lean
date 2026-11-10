module

public import ArtinMatthews.SourceReflectionExpansion
public import ArtinMatthews.QuadraticHeckeFiniteEnergy
public import ArtinMatthews.SourceReflectionIdealCutoffs
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Star.Real
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
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init
public import OAI.NumberTheory.DirichletL.QuadraticSieve.GcdReduction


set_option backward.privateInPublic true
@[expose] public section

/-! The B2 energy and B3 common-ideal blocks for the actual quadratic
kernel. A fixed finite labeling supplies the class slices. -/

namespace ArtinMatthews.SourceEulerAssembly
noncomputable section
open NumberField IsDedekindDomain
open scoped NumberField Classical BigOperators

variable (F : Type) [Field F] [NumberField F]
variable (S₀ : Finset (HeightOneSpectrum (𝓞 F))) {ζ : F} (hζ : IsPrimitiveRoot ζ 12)

local notation "E" => SourcePrimeExponents F S₀
local notation "q" => sourcePrimeExponentNorm F S₀
local notation "χ" => sourceReflectionQuadraticSymbol F S₀ hζ

def sourceQuadraticB2Columns (N : ℝ) : Finset E :=
  (sourceReflectionBoundedExponents F S₀ N).filter sourceReflectionIsSquarefree

def sourceQuadraticB2Rows (M K : ℝ) : Finset E :=
  (sourceReflectionBoundedExponents F S₀ (5 * M / 2)).filter
    (fun a => M / 2 ≤ (q a : ℝ) ∧ K < (q (sourceReflectionParity a) : ℝ))

def sourceQuadraticB2SharpRows (M K : ℝ) : Finset E :=
  (sourceReflectionBoundedExponents F S₀ (2 * M)).filter
    (fun a => M ≤ (q a : ℝ) ∧ K < (q (sourceReflectionParity a) : ℝ))

theorem sourceQuadratic_mem_B2Columns {N : ℝ} (hN : 0 ≤ N) (b : E) :
    b ∈ sourceQuadraticB2Columns F S₀ N ↔ (q b : ℝ) ≤ N ∧ sourceReflectionIsSquarefree b := by
  rw [sourceQuadraticB2Columns, Finset.mem_filter, sourceReflection_mem_boundedExponents F S₀ hN]

theorem sourceQuadratic_mem_B2Rows {M K : ℝ} (hM : 0 ≤ M) (a : E) :
    a ∈ sourceQuadraticB2Rows F S₀ M K ↔
      (q a : ℝ) ≤ 5 * M / 2 ∧ M / 2 ≤ (q a : ℝ) ∧ K < (q (sourceReflectionParity a) : ℝ) := by
  rw [sourceQuadraticB2Rows, Finset.mem_filter,
    sourceReflection_mem_boundedExponents F S₀ (by positivity)]

def sourceQuadraticB2Energy (rows cols : Finset E) (w : E → ℝ) (a : E → ℂ) : ℝ :=
  ∑ d ∈ rows, w d * ‖QuadraticScale.rowValue cols χ a d‖ ^ 2

def sourceQuadraticCommonIdeals (cols : Finset E) : Finset E :=
  (cols ×ˢ cols).image (fun p : E × E => p.1 ⊓ p.2)

def sourceQuadraticPairValue (a : E → ℂ) (d : E) (p : E × E) : ℂ :=
  star (χ d p.1 * a p.1) * (χ d p.2 * a p.2)

def sourceQuadraticB3Block (rows cols : Finset E) (w : E → ℝ) (a : E → ℂ) (g : E) : ℂ :=
  ∑ d ∈ rows, (w d : ℂ) *
    ∑ p ∈ (cols ×ˢ cols).filter (fun p : E × E => p.1 ⊓ p.2 = g),
      sourceQuadraticPairValue F S₀ hζ a d p

def sourceQuadraticClassColumns {G : Type*} [DecidableEq G]
    (cols : Finset E) (label : E → G) (c : G) : Finset E :=
  cols.filter (fun b => label b = c)

theorem sourceQuadraticB2SharpEnergy_le_smoothed (M K : ℝ) (hM : 0 < M)
    (W : ℝ → ℝ) (hW : ∀ t, 0 ≤ W t) (hWdyad : ∀ t ∈ Set.Icc (1 : ℝ) 2, 1 ≤ W t)
    (cols : Finset E) (a : E → ℂ) :
    sourceQuadraticB2Energy F S₀ hζ (sourceQuadraticB2SharpRows F S₀ M K) cols (fun _ => 1) a ≤
      sourceQuadraticB2Energy F S₀ hζ (sourceQuadraticB2Rows F S₀ M K) cols
        (fun d => W ((q d : ℝ) / M)) a := by
  have hmem (d : E) (hd : d ∈ sourceQuadraticB2SharpRows F S₀ M K) :
      M ≤ (q d : ℝ) ∧ (q d : ℝ) ≤ 2 * M ∧ K < (q (sourceReflectionParity d) : ℝ) := by
    obtain ⟨hu, hl, hk⟩ := Finset.mem_filter.mp hd
    exact ⟨hl, (sourceReflection_mem_boundedExponents F S₀ (by positivity) d).mp hu, hk⟩
  unfold sourceQuadraticB2Energy
  calc
    _ ≤ ∑ d ∈ sourceQuadraticB2SharpRows F S₀ M K,
        W ((q d : ℝ) / M) * ‖QuadraticScale.rowValue cols χ a d‖ ^ 2 := by
      apply Finset.sum_le_sum
      intro d hd
      obtain ⟨hl, hu, _⟩ := hmem d hd
      exact mul_le_mul_of_nonneg_right (hWdyad _ ⟨
        (le_div_iff₀ hM).mpr (by simpa only [one_mul] using hl),
        (div_le_iff₀ hM).mpr hu⟩) (sq_nonneg _)
    _ ≤ _ := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro d hd
        obtain ⟨hl, hu, hk⟩ := hmem d hd
        exact (sourceQuadratic_mem_B2Rows F S₀ hM.le d).mpr ⟨
          hu.trans (by linarith), (by linarith : M / 2 ≤ M).trans hl, hk⟩
      · exact fun d _ _ => mul_nonneg (hW _) (sq_nonneg _)

theorem sourceQuadratic_row_square_eq_pairs (cols : Finset E) (a : E → ℂ) (d : E) :
    ((‖QuadraticScale.rowValue cols χ a d‖ ^ 2 : ℝ) : ℂ) =
      ∑ p ∈ cols ×ˢ cols, sourceQuadraticPairValue F S₀ hζ a d p := by
  let z (b : E) := χ d b * a b
  change ((‖∑ b ∈ cols, z b‖ ^ 2 : ℝ) : ℂ) =
    ∑ p ∈ cols ×ˢ cols, star (z p.1) * z p.2
  rw [← Finset.sum_coe_sort cols z, Finset.sum_product]
  calc
    _ = ∑ j : cols, ∑ k : cols, star (z j.val) * z k.val :=
      OAI.CoprimeSieveOperator.square_norm_sum (fun b : cols => z b.val)
    _ = ∑ j : cols, ∑ k ∈ cols, star (z j.val) * z k :=
      Finset.sum_congr rfl (fun j _ => Finset.sum_coe_sort cols (fun k => star (z j.val) * z k))
    _ = _ := Finset.sum_coe_sort cols (fun b => ∑ k ∈ cols, star (z b) * z k)

theorem sourceQuadraticB2Energy_eq_common_sum (rows cols : Finset E) (w : E → ℝ) (a : E → ℂ) :
    (sourceQuadraticB2Energy F S₀ hζ rows cols w a : ℂ) =
      ∑ g ∈ sourceQuadraticCommonIdeals F S₀ cols, sourceQuadraticB3Block F S₀ hζ rows cols w a g := by
  let G := sourceQuadraticCommonIdeals F S₀ cols
  let P := cols ×ˢ cols
  let g (p : E × E) := p.1 ⊓ p.2
  have hmaps (p : E × E) (hp : p ∈ P) : g p ∈ G := Finset.mem_image_of_mem g hp
  unfold sourceQuadraticB2Energy
  calc
    _ = ∑ d ∈ rows, (w d : ℂ) * ∑ p ∈ P, sourceQuadraticPairValue F S₀ hζ a d p := by
      simp only [Complex.ofReal_sum, Complex.ofReal_mul, sourceQuadratic_row_square_eq_pairs, P]
    _ = ∑ d ∈ rows, ∑ c ∈ G, (w d : ℂ) *
        ∑ p ∈ P.filter (fun p => g p = c), sourceQuadraticPairValue F S₀ hζ a d p := by
      apply Finset.sum_congr rfl
      intro d _
      rw [← Finset.sum_fiberwise_of_maps_to hmaps, Finset.mul_sum]
    _ = _ := Finset.sum_comm

theorem sourceQuadraticB2Energy_le_class_sum {G : Type*} [Fintype G] [DecidableEq G]
    (rows cols : Finset E) (w : E → ℝ) (hw : ∀ d ∈ rows, 0 ≤ w d)
    (a : E → ℂ) (label : E → G) :
    sourceQuadraticB2Energy F S₀ hζ rows cols w a ≤
      (Fintype.card G : ℝ) * ∑ c : G, sourceQuadraticB2Energy F S₀ hζ rows
        (sourceQuadraticClassColumns F S₀ cols label c) w a := by
  let σ (b : cols) := label b.val
  let coeff (b : cols) := a b.val
  have h := OAI.FiniteSieveRestriction.sector_weighted_energy_bound
    (fun (d : rows) (b : cols) => χ d.val b.val) σ coeff (fun d => w d.val)
    (fun d => hw d.val d.property)
  have hslice (d : rows) (c : G) :
      (∑ b : cols, χ d.val b.val * OAI.FiniteSieveRestriction.sectorCoefficient σ c coeff b) =
        QuadraticScale.rowValue (sourceQuadraticClassColumns F S₀ cols label c) χ a d.val := by
    simp only [OAI.FiniteSieveRestriction.sectorCoefficient, σ, coeff, mul_ite, mul_zero]
    rw [Finset.sum_coe_sort cols (fun b => if label b = c then χ d.val b * a b else 0),
      ← Finset.sum_filter]
    rfl
  simp_rw [hslice] at h
  have hfull (d : rows) :
      (∑ b : cols, χ d.val b.val * coeff b) = QuadraticScale.rowValue cols χ a d.val :=
    Finset.sum_coe_sort cols (fun b => χ d.val b * a b)
  simp_rw [hfull] at h
  have henergy (B : Finset E) :
      (∑ d : rows, w d.val * ‖QuadraticScale.rowValue B χ a d.val‖ ^ 2) =
        sourceQuadraticB2Energy F S₀ hζ rows B w a :=
    Finset.sum_coe_sort rows (fun d => w d * ‖QuadraticScale.rowValue B χ a d‖ ^ 2)
  simp_rw [henergy] at h
  exact h

end
end ArtinMatthews.SourceEulerAssembly
