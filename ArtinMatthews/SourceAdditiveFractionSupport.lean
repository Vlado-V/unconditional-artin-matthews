module

public import ArtinMatthews.SourceAdditiveCompactBox
public import ArtinMatthews.SourceReducedFractionLabels
public import ArtinMatthews.SourcePrimeNormSummability
public import ArtinMatthews.VaryingKummerAnalyticIdealModuleFrequencyBalanced
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

/-! Finiteness of the full compact row set and bounded denominator set
from the genuine integral coordinate embedding and quotient norm. -/
namespace ArtinMatthews.SourcePhysical

open NumberField IsDedekindDomain AllowedGenerators SIntegerQuotient VaryingKummerAnalytic
open scoped NumberField Classical
noncomputable section
variable (F : Type) [Field F] [NumberField F]
variable (S₀ : Finset (HeightOneSpectrum (𝓞 F))) {ζ : F}

local notation "Splaces" => sourceHilbertSet F S₀
local notation "T" => sourceHilbertSeed F S₀
local notation "R" => sourceRing F S₀
local notation "E" => SourcePrimeExponents F S₀
local notation "M" => sourcePrimeExponentIdeal F S₀
local notation "q" => sourcePrimeExponentNorm F S₀
local notation "O" => (⊤ : Ideal (𝓞 F))
local notation "J" => IdealModuleFrequencyIndex F O top_ne_bot

theorem sourceScaledLatticeRows_finite (hζ : IsPrimitiveRoot ζ 12)
    (B : Set (SLocalAdditiveCompletionSpace F Splaces)) (hB : IsCompact B) {N : ℝ} (hN : 0 < N) :
    (sourceScaledLatticeRows F S₀ hζ B N).Finite := by
  let A := sourceScaledLatticeRows F S₀ hζ B N
  obtain ⟨δ, hδ, _, C, _, hclear⟩ := exists_sourceScaledLatticeRows_integral F S₀ hζ B hB
  choose n hn hnorm using fun m : A => hclear N hN m.val m.property
  let L := idealModuleIntegerCoordinateConstant F O top_ne_bot * (C * N ^ (Module.finrank ℚ F : ℝ)⁻¹)
  let v (z : J → ℤ) (j : J) : ℝ := z j
  let D : Set (J → ℤ) := v ⁻¹' Metric.closedBall 0 L
  have hc : IsCompact D :=
    (Topology.IsClosedEmbedding.piMap (fun _ : J => Int.isClosedEmbedding_coe_real)).isCompact_preimage
      (isCompact_closedBall 0 L)
  let : Finite D := hc.finite_of_discrete
  let c (m : A) := idealModuleIntegerCoordinates F O top_ne_bot ⟨n m, by simp⟩
  have hmem (m : A) : c m ∈ D := by
    change v (c m) ∈ Metric.closedBall 0 L
    rw [Metric.mem_closedBall, dist_zero_right]
    exact (idealModuleIntegerCoordinates_norm_le F O top_ne_bot ⟨n m, by simp⟩).trans
      (mul_le_mul_of_nonneg_left (hnorm m) (idealModuleIntegerCoordinateConstant_pos F O top_ne_bot).le)
  have hi : Function.Injective (fun m : A => (⟨c m, hmem m⟩ : D)) := by
    intro m m' hm
    have hcoord : c m = c m' := congrArg Subtype.val hm
    have he := idealModuleIntegerCoordinates_injective F O top_ne_bot hcoord
    have hval := congrArg (fun z : O => (z.val : F)) he
    change (n m : F) = (n m' : F) at hval
    rw [hn m, hn m'] at hval
    exact Subtype.ext (Subtype.ext (mul_right_cancel₀ (Subtype.coe_injective.ne hδ) hval))
  let : Finite A := Finite.of_injective _ hi
  exact Set.toFinite A

theorem sourceReducedFractionLabel_finite_cutoff (a : E → R)
    (hgen : ∀ e, (sourcePrimeExponentRingIdealEquiv F S₀ e).val = Ideal.span {a e}) (V : ℝ) :
    {p : SourceReducedFractionLabel F S₀ a | (q p.1 : ℝ) ≤ V}.Finite := by
  let D : Set E := {e : E | (q e : ℝ) ≤ V}
  have hD : D.Finite := by
    apply ((Ideal.finite_setOfPred_absNorm_le (S := 𝓞 F) ⌈V⌉₊).preimage
      (sourcePrimeExponentIdeal_injective F S₀).injOn).subset
    intro e he
    change (q e : ℝ) ≤ V at he
    change Ideal.absNorm (M e) ≤ ⌈V⌉₊
    rw [sourcePrimeExponentIdeal_norm]
    exact_mod_cast he.trans (Nat.le_ceil V)
  let : Finite D := hD
  have hFinite (e : D) : Finite ((R ⧸ Ideal.span {a e.val})ˣ) := by
    have h : Nat.card (R ⧸ Ideal.span {a e.val}) = q e.val := by
      calc
        _ = Nat.card (R ⧸ (M e.val).map (algebraMap (𝓞 F) R)) :=
          Nat.card_congr (Ideal.quotEquivOfEq (hgen e.val).symm).toEquiv
        _ = Ideal.absNorm (M e.val) := principal_quotient_card T _
          (sourcePrimeExponentIdeal_exterior F S₀ e.val).2
        _ = _ := sourcePrimeExponentIdeal_norm F S₀ e.val
    let : Finite (R ⧸ Ideal.span {a e.val}) :=
      Nat.finite_of_card_ne_zero (h.trans_ne (sourcePrimeExponentNorm_pos F S₀ e.val).ne')
    exact Finite.of_injective Units.val Units.val_injective
  let P : Set (SourceReducedFractionLabel F S₀ a) := {p | (q p.1 : ℝ) ≤ V}
  let f (p : P) : Σ e : D, (R ⧸ Ideal.span {a e.val})ˣ := ⟨⟨p.val.1, p.property⟩, p.val.2⟩
  let g (p : Σ e : D, (R ⧸ Ideal.span {a e.val})ˣ) : SourceReducedFractionLabel F S₀ a :=
    ⟨p.1.val, p.2⟩
  have hi : Function.Injective f := fun _ _ h => Subtype.ext (congrArg g h)
  let : Finite P := Finite.of_injective f hi
  exact Set.toFinite P

end
end ArtinMatthews.SourcePhysical
