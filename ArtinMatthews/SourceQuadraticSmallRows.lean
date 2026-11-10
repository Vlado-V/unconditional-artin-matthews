module

public import ArtinMatthews.SourceQuadraticBlockIdeals
public import ArtinMatthews.QuadraticHeckeCutoffSplit
public import ArtinMatthews.QuadraticHeckeSmallResidue
public import ArtinMatthews.SourceReflectionExteriorRows
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

/-! Exact finite exterior rows for the Small squarefree ideal sum. -/
namespace ArtinMatthews.SourceEulerAssembly
open NumberField IsDedekindDomain
open scoped NumberField Classical BigOperators
noncomputable section

variable (F : Type) [Field F] [NumberField F]
variable (S₀ : Finset (HeightOneSpectrum (𝓞 F)))
local notation "E" => SourcePrimeExponents F S₀
local notation "I" => sourcePrimeExponentIdeal F S₀
local notation "q" => sourcePrimeExponentNorm F S₀

def sourceQuadraticSmallRows (K : ℝ) (g : E) : Finset E :=
  (sourceReflectionBoundedExponents F S₀ K).filter
    (fun a => sourceReflectionIsSquarefree a ∧ Disjoint a.support g.support)

def sourceQuadraticSmallIdeals (K : ℝ) (g : E) : Finset (Ideal (𝓞 F)) :=
  (quadraticHeckeCoprimeCutoff F (I g) K).filter
    (fun a => IsCoprime a (sourceQuadraticBlockBadIdeal F S₀))

theorem sourceQuadraticSmallRows_mem {K : ℝ} (hK : 0 ≤ K) (g a : E) :
    a ∈ sourceQuadraticSmallRows F S₀ K g ↔
      (q a : ℝ) ≤ K ∧ sourceReflectionIsSquarefree a ∧ Disjoint a.support g.support := by
  rw [sourceQuadraticSmallRows, Finset.mem_filter, sourceReflection_mem_boundedExponents F S₀ hK]

theorem sourceQuadraticSmallRows_image {K : ℝ} (hK : 0 ≤ K) (g : E) :
    (sourceQuadraticSmallRows F S₀ K g).image I = sourceQuadraticSmallIdeals F S₀ K g := by
  ext J
  constructor
  · intro hJ
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hJ
    obtain ⟨hn, hsf, hd⟩ := (sourceQuadraticSmallRows_mem F S₀ hK g a).mp ha
    apply Finset.mem_filter.mpr
    refine ⟨(mem_quadraticHeckeCoprimeCutoff F).mpr ⟨?_, ?_, ?_⟩,
      sourceQuadraticBlock_exterior_coprime F S₀ a⟩
    · exact (sourceReflectionExteriorIdeal_squarefree F S₀ a).mpr hsf
    · simpa only [sourcePrimeExponentIdeal_norm] using hn
    · exact (sourceQuadraticBlock_ideal_coprime_iff F S₀ a g).mpr hd
  · intro hJ
    obtain ⟨hc, hb⟩ := Finset.mem_filter.mp hJ
    obtain ⟨hsf, hn, hg⟩ := (mem_quadraticHeckeCoprimeCutoff F).mp hc
    let J₀ : {J : Ideal (𝓞 F) // J ≠ ⊥} := ⟨J, hsf.ne_zero⟩
    obtain ⟨a, ha⟩ := (sourceQuadraticBlockExteriorEquiv F S₀).surjective ⟨J₀, hb⟩
    have hI : I a = J := congrArg (fun x => x.val.val) ha
    apply Finset.mem_image.mpr
    refine ⟨a, (sourceQuadraticSmallRows_mem F S₀ hK g a).mpr ⟨?_, ?_, ?_⟩, hI⟩
    · rw [← hI, sourcePrimeExponentIdeal_norm] at hn
      exact hn
    · apply (sourceReflectionExteriorIdeal_squarefree F S₀ a).mp
      rwa [hI]
    · apply (sourceQuadraticBlock_ideal_coprime_iff F S₀ a g).mp
      rwa [hI]

theorem sourceQuadraticSmallRows_sum {K : ℝ} (hK : 0 ≤ K) (g : E)
    {A : Type*} [AddCommMonoid A] (f : Ideal (𝓞 F) → A) :
    (∑ J ∈ sourceQuadraticSmallIdeals F S₀ K g, f J) =
      ∑ a ∈ sourceQuadraticSmallRows F S₀ K g, f (I a) := by
  rw [← sourceQuadraticSmallRows_image F S₀ hK g,
    Finset.sum_image (sourcePrimeExponentIdeal_injective F S₀).injOn]

theorem sourceQuadraticSmallRows_tsum {K : ℝ} (hK : 0 ≤ K) (g : E)
    (f : Ideal (𝓞 F) → ℂ) :
    (∑' a : {J : Ideal (𝓞 F) // Squarefree J},
      if IsCoprime a.val (sourceQuadraticBlockBadIdeal F S₀) ∧ IsCoprime a.val (I g) ∧
        (Ideal.absNorm a.val : ℝ) ≤ K then f a.val else 0) =
      ∑ a ∈ sourceQuadraticSmallRows F S₀ K g, f (I a) := by
  rw [quadraticHeckeSquarefreeCutoff_masked_tsum F (I g) (sourceQuadraticBlockBadIdeal F S₀) K f]
  rw [← sourceQuadraticSmallRows_sum F S₀ hK g f]
  exact (Finset.sum_filter ..).symm

theorem sourceQuadraticSmallRows_empty {K : ℝ} (hK : 0 ≤ K) (hK1 : K < 1) (g : E) :
    sourceQuadraticSmallRows F S₀ K g = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro a ha
  have hn := ((sourceQuadraticSmallRows_mem F S₀ hK g a).mp ha).1
  have hpos := sourceReflection_norm_one_le F S₀ a
  linarith

end
end ArtinMatthews.SourceEulerAssembly
