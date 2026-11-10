module

public import ArtinMatthews.SourcePoissonProbeRowBox
public import ArtinMatthews.SourceAdditiveCompactBox
public import ArtinMatthews.SourceFrequencyFactorization
public import ArtinMatthews.SourceScaledRowIdealFiber
public import ArtinMatthews.SourceScaledRowProductNorm
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

namespace ArtinMatthews.SourceEulerAssembly
open NumberField IsDedekindDomain AllowedGenerators SourcePhysical Set
open scoped NumberField Classical
noncomputable section

variable (F : Type) [Field F] [NumberField F] [IsTotallyComplex F]
variable (S₀ : Finset (HeightOneSpectrum (𝓞 F))) {ζ : F} (hζ : IsPrimitiveRoot ζ 12)
local notation "S" => sourceHilbertSet F S₀
local notation "A" => SLocalAdditiveCompletionSpace F S
local notation "R" => sourceRing F S₀
local notation "E" => SourcePrimeExponents F S₀
local notation "U" => SourceNonzeroFrequency F S₀
local notation "B" => sourcePoissonLogRowBox F S₀ hζ
local notation "Rows" => sourceScaledLatticeRows F S₀ hζ B

theorem sourcePoissonLogRowBox_away_zero {y : A} (hy : y ∈ B) :
    (∀ w : InfinitePlace F, y.1 w ≠ 0) ∧ (∀ p : S, y.2 p ≠ 0) := by
  obtain ⟨⟨t, x⟩, hx, rfl⟩ := hy
  have h := sourceProbeEnlargedAnnulus_away_zero F hζ S hx.2
  exact ⟨fun w => mul_ne_zero ((t.val.1 w).ne_zero) (h.1 w),
    fun p => mul_ne_zero ((t.val.2 p).ne_zero) (h.2 p)⟩

theorem sourcePoissonLogRows_ne_zero {N : ℝ} {m : R} (hm : m ∈ Rows N) : m ≠ 0 := by
  intro hz
  subst m
  obtain ⟨y, hy, he⟩ := hm
  let w : InfinitePlace F := Classical.arbitrary _
  have h := congrArg (fun z : A => z.1 w) he
  rw [show (((0 : R) : F)) = 0 from rfl, map_zero] at h
  exact mul_ne_zero ((sLocalPositiveScaling F hζ S N).1 w).ne_zero
    ((sourcePoissonLogRowBox_away_zero F S₀ hζ hy).1 w) h

/-- The actual exterior data on the shared physical box, uniform in the radial scale. -/
theorem sourcePoissonLogRows_exteriorData :
    ∃ K : ℝ, 1 ≤ K ∧ ∃ C : ℕ, ∀ N : ℝ, 0 < N →
      (∀ m : U, m.val ∈ Rows N →
        (sourcePrimeExponentNorm F S₀ (sourceElementExponents F S₀ m.val m.property) : ℝ) ≤ K * N) ∧
      ∀ M : Finset U, (∀ m ∈ M, m.val ∈ Rows N) → ∀ e : E,
        (M.filter (fun m => sourceElementExponents F S₀ m.val m.property = e)).card ≤ C := by
  have hB := sourcePoissonLogRowBox_isCompact F S₀ hζ
  obtain ⟨K, hK, hnorm⟩ := sourceScaledLatticeRows_exteriorNorm_bound F S₀ hζ B hB
  obtain ⟨C, hcard⟩ := sourceScaledLatticeRows_exteriorFibers_card_le F S₀ hζ B hB
    (fun _ h => sourcePoissonLogRowBox_away_zero F S₀ hζ h)
  exact ⟨K, hK, C, fun N hN => ⟨hnorm N hN, hcard N⟩⟩

/-- The same uniform exterior data on the literal source-ring rows, with the
nonzero proof derived from membership in the actual annular row box. -/
theorem sourcePoissonLogRows_exteriorData_raw :
    ∃ K : ℝ, 1 ≤ K ∧ ∃ C : ℕ, ∀ N : ℝ, 0 < N →
      (∀ m : R, ∀ hm : m ∈ Rows N,
        (sourcePrimeExponentNorm F S₀ (sourceElementExponents F S₀ m
          (sourcePoissonLogRows_ne_zero F S₀ hζ hm)) : ℝ) ≤ K * N) ∧
      ∀ M : Finset R, (∀ m ∈ M, m ∈ Rows N) → ∀ e : E,
        (M.filter (fun m => ∃ hm : m ≠ 0, sourceElementExponents F S₀ m hm = e)).card ≤ C := by
  obtain ⟨K, hK, C, h⟩ := sourcePoissonLogRows_exteriorData F S₀ hζ
  refine ⟨K, hK, C, fun N hN => ⟨fun m hm => (h N hN).1 ⟨m, sourcePoissonLogRows_ne_zero F S₀ hζ hm⟩ hm,
    fun M hM e => ?_⟩⟩
  let T := M.filter (fun m => ∃ hm : m ≠ 0, sourceElementExponents F S₀ m hm = e)
  let f (m : T) : U := ⟨m.val, (Finset.mem_filter.mp m.property).2.choose⟩
  have hf : Function.Injective f := fun _ _ he => Subtype.ext (congrArg (fun z : U => z.val) he)
  let T' := T.attach.image f
  have hT' (m : U) (hm : m ∈ T') : m.val ∈ Rows N := by
    obtain ⟨m', _, rfl⟩ := Finset.mem_image.mp hm
    exact hM m'.val (Finset.mem_filter.mp m'.property).1
  have hfilter : (T'.filter (fun m => sourceElementExponents F S₀ m.val m.property = e)) = T' := by
    apply Finset.filter_eq_self.mpr
    intro m hm
    obtain ⟨m', _, rfl⟩ := Finset.mem_image.mp hm
    exact (Finset.mem_filter.mp m'.property).2.choose_spec
  have hc := (h N hN).2 T' hT' e
  rw [hfilter] at hc
  change T.card ≤ C
  simpa only [T', Finset.card_image_of_injective _ hf, Finset.card_attach] using hc

end
end ArtinMatthews.SourceEulerAssembly
