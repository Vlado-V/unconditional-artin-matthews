module

/- Adapted in the Artin–Matthews source bundle. The source, upstream and packaged digests are recorded in SOURCE_MANIFEST.json. -/

public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.MeasureTheory.Measure.FiniteMeasureExt
public import Mathlib.RingTheory.PiTensorProduct
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.CStarAlgebra.ContinuousMap
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Topology.Sheaves.Init
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.ENatToNat
public import Mathlib.Tactic.Basify


set_option backward.privateInPublic true
@[expose] public section

/-! # Character Measure -/

namespace OAI.RepresentationTheory.Weil.Local.CharacterMeasure

noncomputable section

/-! A point-separating family of bounded continuous characters determines
finite measures. This avoids any classification of archimedean characters. -/

open _root_.MeasureTheory BoundedContinuousFunction
open scoped BigOperators

variable {X I : Type} [PseudoEMetricSpace X] [AddCommGroup I]
variable (χ : I → X →ᵇ ℂ)
variable (hzero : χ 0 = 1) (hadd : ∀ i j, χ (i + j) = χ i * χ j)
variable (hneg : ∀ i, χ (-i) = star (χ i))

def characterSpan : Submodule ℂ (X →ᵇ ℂ) := Submodule.span ℂ (Set.range χ)

include hadd in
theorem characterSpan_mul {f g : X →ᵇ ℂ}
    (hf : f ∈ characterSpan χ) (hg : g ∈ characterSpan χ) :
    f * g ∈ characterSpan χ := by
  have hgen (i : I) {g : X →ᵇ ℂ} (hg : g ∈ characterSpan χ) :
      χ i * g ∈ characterSpan χ := by
    induction hg using Submodule.span_induction with
    | mem g hg =>
        obtain ⟨j, rfl⟩ := hg
        rw [← hadd]
        exact Submodule.subset_span ⟨i + j, rfl⟩
    | zero => simp
    | add g h _ _ hg hh => simpa [mul_add] using (characterSpan χ).add_mem hg hh
    | smul c g _ hg => simpa [mul_smul_comm] using (characterSpan χ).smul_mem c hg
  induction hf using Submodule.span_induction with
  | mem f hf =>
      obtain ⟨i, rfl⟩ := hf
      exact hgen i hg
  | zero => simp
  | add f h _ _ hf hh => simpa [add_mul] using (characterSpan χ).add_mem hf hh
  | smul c f _ hf => simpa [smul_mul_assoc] using (characterSpan χ).smul_mem c hf

include hneg in
theorem characterSpan_star {f : X →ᵇ ℂ} (hf : f ∈ characterSpan χ) :
    star f ∈ characterSpan χ := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
      obtain ⟨i, rfl⟩ := hf
      rw [← hneg]
      exact Submodule.subset_span ⟨-i, rfl⟩
  | zero => simp
  | add f g _ _ hf hg => simpa using (characterSpan χ).add_mem hf hg
  | smul c f _ hf => simpa using (characterSpan χ).smul_mem (star c) hf

def characterAlgebra : StarSubalgebra ℂ (X →ᵇ ℂ) where
  carrier := characterSpan χ
  zero_mem' := (characterSpan χ).zero_mem
  add_mem' := (characterSpan χ).add_mem
  one_mem' := hzero ▸ Submodule.subset_span ⟨0, rfl⟩
  mul_mem' := characterSpan_mul χ hadd
  algebraMap_mem' c := by
    change (algebraMap ℂ (X →ᵇ ℂ)) c ∈ characterSpan χ
    have hone : (1 : X →ᵇ ℂ) ∈ characterSpan χ :=
      hzero ▸ Submodule.subset_span ⟨0, rfl⟩
    simpa only [Algebra.smul_def, mul_one] using (characterSpan χ).smul_mem c hone
  star_mem' := characterSpan_star χ hneg

theorem characterAlgebra_separates
    (hsep : ∀ x y : X, x ≠ y → ∃ i, χ i x ≠ χ i y) :
    ((characterAlgebra χ hzero hadd hneg).map (toContinuousMapStarₐ ℂ)).SeparatesPoints := by
  intro x y hxy
  obtain ⟨i, hi⟩ := hsep x y hxy
  use χ i
  simp only [StarSubalgebra.coe_toSubalgebra, StarSubalgebra.coe_map, Set.mem_image,
    SetLike.mem_coe, exists_exists_and_eq_and, ne_eq]
  exact ⟨⟨χ i, Submodule.subset_span ⟨i, rfl⟩, rfl⟩, hi⟩

include hzero hadd hneg in
theorem measures_eq_of_character_integrals
    [MeasurableSpace X] [BorelSpace X]
    [CompleteSpace X] [SecondCountableTopology X]
    (hsep : ∀ x y : X, x ≠ y → ∃ i, χ i x ≠ χ i y)
    (μ ν : Measure X) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (h : ∀ i, ∫ x, χ i x ∂μ = ∫ x, χ i x ∂ν) : μ = ν := by
  apply ext_of_forall_mem_subalgebra_integral_eq_of_pseudoEMetric_complete_countable
    (characterAlgebra_separates χ hzero hadd hneg hsep)
  intro f hf
  change f ∈ characterSpan χ at hf
  induction hf using Submodule.span_induction with
  | mem f hf =>
      obtain ⟨i, rfl⟩ := hf
      exact h i
  | zero => simp
  | add f g _ _ hf hg =>
      simp only [coe_add, Pi.add_apply]
      rw [integral_add (f.integrable μ) (g.integrable μ),
        integral_add (f.integrable ν) (g.integrable ν), hf, hg]
  | smul c f _ hf =>
      simp only [coe_smul, integral_smul, hf]

end

end OAI.RepresentationTheory.Weil.Local.CharacterMeasure
