module

public import ArtinMatthews.SourceKPAllowedClassGate
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
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
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.RegularLocalRing.Defs
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
public import Mathlib.Topology.Separation.CompletelyRegular
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! Insert the finite-class gate in the actual whole-local positive
frequency expansion, retaining its pointwise summability. -/
namespace ArtinMatthews
open NumberField IsDedekindDomain AllowedGenerators SourceReflection MeasureTheory
open scoped NumberField Classical BigOperators
noncomputable section

variable (K : Type) [Field K] [NumberField K]
variable {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
variable (S₀ : Finset (HeightOneSpectrum (𝓞 K)))
local notation "S" => sourceHilbertSet K S₀
local notation "U" => SWholeUnits K S
local notation "A" => allowedSubgroup K hζ S₀

/-- The factor outside the retained cutoffs keeps its full local argument. -/
def sourceKPForwardRetainedTerm
    (W : ∀ P : S, SourceThetaFiniteCutoff K P.val) (F : Kˣ → U → ℂ) (m : Kˣ) (x : U) : ℂ :=
  let z := sWholeDiagonal K S m * x
  F m z * ∏ P : S, (W P).factor (z.2 P)

def sourceKPAllowedForwardSeries
    (W : ∀ P : S, SourceThetaFiniteCutoff K P.val) (F : Kˣ → U → ℂ) (x : U) : ℂ :=
  sourceKPAllowedClassGate K hζ S₀ x * ∑' m, sourceKPForwardRetainedTerm K S₀ W F m x

theorem sourceKPAllowedClassGate_hasSum
    (W : ∀ P : S, SourceThetaFiniteCutoff K P.val)
    (hW : ∀ (P : S) (t : (P.val.adicCompletion K)ˣ), t ∈ (W P).region → ∃ w, w^6 = t)
    (F : Kˣ → U → ℂ) (x : U) {s₀ : ℂ}
    (hF : HasSum (fun m => sourceKPForwardRetainedTerm K S₀ W F m x) s₀) :
    HasSum (fun m => if m ∈ A then sourceKPForwardRetainedTerm K S₀ W F m x else 0)
      (sourceKPAllowedClassGate K hζ S₀ x * s₀) := by
  apply (hF.mul_left (sourceKPAllowedClassGate K hζ S₀ x)).congr_fun
  intro m
  symm
  have hg := sourceKPAllowedClassGate_mul_retainedProduct K hζ S₀ W hW m x
  unfold sourceKPForwardRetainedTerm
  dsimp only
  rw [mul_left_comm, hg]
  split_ifs <;> simp

theorem sourceKPForwardRetainedTerm_measurable [MeasurableSpace U] [BorelSpace U]
    (W : ∀ P : S, SourceThetaFiniteCutoff K P.val) (F : Kˣ → U → ℂ)
    (m : Kˣ) (hF : Measurable (F m)) :
    Measurable (sourceKPForwardRetainedTerm K S₀ W F m) := by
  let z (x : U) := sWholeDiagonal K S m * x
  have hz : Continuous z := continuous_const.mul continuous_id
  apply (hF.comp hz.measurable).mul
  apply Finset.measurable_prod
  intro P _
  let p (x : U) := (z x).2 P
  have hp : Continuous p := (continuous_apply P).comp (continuous_snd.comp hz)
  exact measurable_const.indicator ((W P).isOpen.preimage hp).measurableSet

theorem sourceKPAllowedForwardSeries_measurable [MeasurableSpace U] [BorelSpace U]
    (W : ∀ P : S, SourceThetaFiniteCutoff K P.val) (F : Kˣ → U → ℂ)
    (hF : ∀ m, Measurable (F m)) :
    Measurable (sourceKPAllowedForwardSeries K hζ S₀ W F) := by
  let : Countable K := (Module.finBasis ℚ K).repr.injective.countable
  let : Countable Kˣ := Units.val_injective.countable
  exact (sourceKPAllowedClassGate_measurable K hζ S₀).mul
    (Measurable.tsum fun m => sourceKPForwardRetainedTerm_measurable K S₀ W F m (hF m))

end
end ArtinMatthews
