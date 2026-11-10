module

public import ArtinMatthews.SourceReflectionNumeratorReindex
public import ArtinMatthews.SourceReflectionSeries
public import ArtinMatthews.SourcePrimeExponentValuation
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

/-! The original series extends the allowed numerator support by zero.
At a shared row and column prime this zero comes from the actual
quadratic residue symbol. -/
namespace ArtinMatthews.SourceEulerAssembly

open NumberField IsDedekindDomain VaryingKummerAnalytic SIntegerQuotient
open scoped NumberField BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable Classical.decEq

variable (F : Type) [Field F] [NumberField F]
variable (S₀ : Finset (HeightOneSpectrum (𝓞 F))) {ζ : F} (hζ : IsPrimitiveRoot ζ 12)
local notation "Prime" => SourceExteriorPrime F S₀
local notation "E" => SourcePrimeExponents F S₀

theorem sourceReflectionQuadraticSymbol_zero_of_common (d c : E)
    (hd : sourceReflectionIsSquarefree d) (P : Prime)
    (hP : P ∈ d.support) (hPc : c P ≠ 0) :
    sourceReflectionQuadraticSymbol F S₀ hζ d c = 0 := by
  let χ := reflectionPrimeCharacters F hζ S₀
  let g := sourcePrimeExponentGenerator F hζ S₀ c
  have hP₁ : d P = 1 := by
    have h := hd P
    have hn := Finsupp.mem_support_iff.mp hP
    omega
  have hg : g ∈ primePowerIdeal (sourceHilbertSeed F S₀) P.val 1 :=
    (sourcePrimeExponentGenerator_mem_primePower_iff F hζ S₀ c P 1).mpr
      (Nat.one_le_iff_ne_zero.mpr hPc)
  have hq : Ideal.Quotient.mk (primePowerIdeal (sourceHilbertSeed F S₀) P.val 1) g = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr hg
  have hzero : sourcePrimeExponentLocalWeight F hζ S₀ χ P (d P) g = 0 := by
    rw [hP₁, sourcePrimeExponentLocalWeight]
    unfold sourceLocalPowerWeight
    rw [hq]
    erw [map_zero, generatorPowerWeight_eq_transport, map_zero]
    simpa using probePowerResidueWeight_succ_zero F P.val (χ P) 0 (0 : 𝓞 F) (Ideal.zero_mem _)
  unfold sourceReflectionQuadraticSymbol reflectionExponentResidueValue sourcePrimeExponentWeight
  rw [Finsupp.prod, Finset.prod_eq_zero hP hzero]
  norm_num

def sourceReflectionTermSupported (f : Finset Prime) (d : E)
    (i : SourceReflectionTermIndex F S₀ f) : Prop :=
  (∀ P ∈ f, i.1.val P % 3 ≤ 1 ∧ i.2.1 P = 0 ∧ i.2.2.val P = 0) ∧
    ∀ P ∈ d.support, i.1.val P = 0 ∧ i.2.1 P = 0 ∧ i.2.2.val P = 0

variable {U : Type} (A : SourceReflectionExpansionData F S₀ U)

theorem sourceReflectionExpansionTerm_zero_of_unsupported
    (Z : ℝ) (h d : E) (hd : sourceReflectionIsSquarefree d)
    (f : Finset Prime) (u : U) (i : SourceReflectionTermIndex F S₀ f)
    (hscalar : ∀ P ∈ f, (1 < i.1.val P % 3 ∨ i.2.1 P ≠ 0) →
      A.scalar h f i.1.val i.2.1 u = 0)
    (hrow : ∀ P ∈ d.support, (i.1.val P ≠ 0 ∨ i.2.1 P ≠ 0) →
      A.row h f i.1.val i.2.1 u d = 0)
    (hcolumn : ∀ P ∈ f, i.2.2.val P ≠ 0 → A.column h f i.1.val i.2.1 u i.2.2.val = 0)
    (hbad : ¬ sourceReflectionTermSupported F S₀ f d i) :
    sourceReflectionExpansionTerm F S₀ hζ A Z h d f i.1.val i.2.1 i.2.2.val u = 0 := by
  by_contra ht
  apply hbad
  have hs : A.scalar h f i.1.val i.2.1 u ≠ 0 := fun hz =>
    ht (by simp [sourceReflectionExpansionTerm, hz])
  have hr : A.row h f i.1.val i.2.1 u d ≠ 0 := fun hz =>
    ht (by simp [sourceReflectionExpansionTerm, hz])
  have hc : A.column h f i.1.val i.2.1 u i.2.2.val ≠ 0 := fun hz =>
    ht (by simp [sourceReflectionExpansionTerm, sourceReflectionColumnCoefficient, hz])
  refine ⟨fun P hP => ⟨le_of_not_gt (fun hx => hs (hscalar P hP (Or.inl hx))),
    not_ne_iff.mp (fun hx => hs (hscalar P hP (Or.inr hx))),
    not_ne_iff.mp (fun hx => hc (hcolumn P hP hx))⟩, ?_⟩
  intro P hP
  refine ⟨not_ne_iff.mp (fun hx => hr (hrow P hP (Or.inl hx))),
    not_ne_iff.mp (fun hx => hr (hrow P hP (Or.inr hx))), ?_⟩
  by_contra hx
  have hz := sourceReflectionQuadraticSymbol_zero_of_common F S₀ hζ d i.2.2.val hd P hP hx
  exact ht (by simp [sourceReflectionExpansionTerm, hz])

theorem sourceReflectionSelectedBranch_eq_numerator
    (Z : ℝ) (h d : E) (f : Finset Prime) (u : U)
    (hzero : ∀ i : SourceReflectionTermIndex F S₀ f, ¬ sourceReflectionTermSupported F S₀ f d i →
      sourceReflectionExpansionTerm F S₀ hζ A Z h d f i.1.val i.2.1 i.2.2.val u = 0) :
    sourceReflectionSelectedBranch F S₀ hζ A Z h d f u (fun _ => True) =
      ∑' e : SourceReflectionNumerator F S₀ d,
        let i := (sourceReflectionNumeratorEquiv F S₀ f d e).val
        sourceReflectionExpansionTerm F S₀ hζ A Z h d f i.1.val i.2.1 i.2.2.val u := by
  let g (i : SourceReflectionTermIndex F S₀ f) :=
    sourceReflectionExpansionTerm F S₀ hζ A Z h d f i.1.val i.2.1 i.2.2.val u
  have hs : Function.support g ⊆ {i | sourceReflectionTermSupported F S₀ f d i} := by
    intro i hi
    by_contra h
    exact hi (hzero i h)
  simp only [sourceReflectionSelectedBranch, ite_true]
  change (∑' i, g i) = ∑' e : SourceReflectionNumerator F S₀ d,
    g (sourceReflectionNumeratorEquiv F S₀ f d e).val
  calc
    _ = ∑' i : SourceReflectionSupportedTermIndex F S₀ f d, g i.val :=
      (tsum_subtype_eq_of_support_subset hs).symm
    _ = _ := ((sourceReflectionNumeratorEquiv F S₀ f d).tsum_eq
      (fun i => g i.val)).symm

end
end ArtinMatthews.SourceEulerAssembly
