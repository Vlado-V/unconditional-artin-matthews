module

public import ArtinMatthews.SourceKPCompactGenuineL2
public import ArtinMatthews.SourceKPTranslateCompactL2
public import Mathlib.Analysis.CStarAlgebra.Module.Constructions
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
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
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

/-! The unnormalized Hecke Gram operators for the actual common finite level. -/
namespace ArtinMatthews
open NumberField MeasureTheory ContinuousLinearMap
open scoped NumberField MatrixGroups AdeleRing InnerProductSpace

noncomputable section

private theorem adjoint_comp_of_norm_sq
    {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
    (P : E →L[ℂ] F) (d : ℝ) (hP : ∀ x, ‖P x‖ ^ 2 = d * ‖x‖ ^ 2) :
    P.adjoint.comp P = (d : ℂ) • ContinuousLinearMap.id ℂ E := by
  have hn (x : E) : (‖P x‖ : ℂ) ^ 2 = (d : ℂ) * (‖x‖ : ℂ) ^ 2 := by
    exact_mod_cast hP x
  ext y
  apply ext_inner_left ℂ
  intro x
  rw [ContinuousLinearMap.comp_apply, P.adjoint_inner_right,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply, inner_smul_right]
  have hp := inner_eq_sum_norm_sq_div_four (𝕜 := ℂ) (P x) (P y)
  have h := inner_eq_sum_norm_sq_div_four (𝕜 := ℂ) x y
  change inner ℂ (P x) (P y) =
    ((‖P x + P y‖ : ℂ) ^ 2 - (‖P x - P y‖ : ℂ) ^ 2 +
      ((‖P x - Complex.I • P y‖ : ℂ) ^ 2 -
        (‖P x + Complex.I • P y‖ : ℂ) ^ 2) * Complex.I) / 4 at hp
  change inner ℂ x y =
    ((‖x + y‖ : ℂ) ^ 2 - (‖x - y‖ : ℂ) ^ 2 +
      ((‖x - Complex.I • y‖ : ℂ) ^ 2 - (‖x + Complex.I • y‖ : ℂ) ^ 2) * Complex.I) / 4 at h
  rw [hp, h, ← P.map_add, ← P.map_sub, ← P.map_smul, ← P.map_sub, ← P.map_add]
  rw [hn, hn, hn, hn]
  ring

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
variable (T : Finset (SourceKPFiniteAdeleProjective K hζ))
include T

local notation "Gf" => SourceKPFiniteAdeleProjective K hζ
local notation "D" => sourceKPFiniteLevelConjugate K hζ
local notation "J" => sourceKPFiniteTranslateLevel K hζ T
local notation "H" => SourceKPGenuineAutomorphicL2 K hζ
local notation "μY" => sourceKPAutomorphicCompactMeasure K hζ (sourceKPArchHaar K hζ)
local notation "μJ" => sourceKPTranslateCompactHaar K hζ T
local notation "LY" => Lp ℂ 2 μY
local notation "LJ" => Lp ℂ 2 μJ

def sourceKPTranslateGenuinePullbackL2 (t : Gf) (ht : J ≤ D t) : H →L[ℂ] LJ :=
  (sourceKPTranslateCompactPullbackL2 K hζ T t ht).comp
    (sourceKPCompactGenuineL2Subspace K hζ (sourceKPArchHaar K hζ)).subtypeL

theorem sourceKPTranslateGenuinePullbackL2_apply (t : Gf) (ht : J ≤ D t) (f : H) :
    sourceKPTranslateGenuinePullbackL2 K hζ T t ht f =
      sourceKPTranslateCompactPullbackL2 K hζ T t ht f.val := rfl

theorem sourceKPTranslateGenuinePullbackL2_norm_sq (t : Gf) (ht : J ≤ D t) (f : H) :
    ‖sourceKPTranslateGenuinePullbackL2 K hζ T t ht f‖ ^ 2 =
      ((J).relIndex (D t) : ℝ) * ‖f‖ ^ 2 :=
  sourceKPTranslateCompactPullbackL2_norm_sq K hζ T t ht f.val

def sourceKPTranslateScalarGramL2 (t : Gf) (ht : J ≤ D t) (u : Gf) (hu : J ≤ D u) :
    LY →L[ℂ] LY :=
  (sourceKPTranslateCompactPullbackL2 K hζ T t ht).adjoint.comp
    (sourceKPTranslateCompactPullbackL2 K hζ T u hu)

def sourceKPTranslateGenuineGramL2 (t : Gf) (ht : J ≤ D t) (u : Gf) (hu : J ≤ D u) :
    H →L[ℂ] H :=
  (sourceKPTranslateGenuinePullbackL2 K hζ T t ht).adjoint.comp
    (sourceKPTranslateGenuinePullbackL2 K hζ T u hu)

theorem sourceKPTranslateScalarGramL2_inner (t : Gf) (ht : J ≤ D t)
    (u : Gf) (hu : J ≤ D u) (f g : LY) :
    inner ℂ (sourceKPTranslateCompactPullbackL2 K hζ T t ht f)
        (sourceKPTranslateCompactPullbackL2 K hζ T u hu g) =
      inner ℂ f (sourceKPTranslateScalarGramL2 K hζ T t ht u hu g) :=
  ((sourceKPTranslateCompactPullbackL2 K hζ T t ht).adjoint_inner_right f _).symm

theorem sourceKPTranslateGenuineGramL2_inner (t : Gf) (ht : J ≤ D t)
    (u : Gf) (hu : J ≤ D u) (f g : H) :
    inner ℂ (sourceKPTranslateGenuinePullbackL2 K hζ T t ht f)
        (sourceKPTranslateGenuinePullbackL2 K hζ T u hu g) =
      inner ℂ f (sourceKPTranslateGenuineGramL2 K hζ T t ht u hu g) :=
  ((sourceKPTranslateGenuinePullbackL2 K hζ T t ht).adjoint_inner_right f _).symm

theorem sourceKPTranslateScalarGramL2_adjoint (t : Gf) (ht : J ≤ D t)
    (u : Gf) (hu : J ≤ D u) :
    (sourceKPTranslateScalarGramL2 K hζ T t ht u hu).adjoint =
      sourceKPTranslateScalarGramL2 K hζ T u hu t ht := by
  simp only [sourceKPTranslateScalarGramL2, adjoint_comp, adjoint_adjoint]

theorem sourceKPTranslateGenuineGramL2_adjoint (t : Gf) (ht : J ≤ D t)
    (u : Gf) (hu : J ≤ D u) :
    (sourceKPTranslateGenuineGramL2 K hζ T t ht u hu).adjoint =
      sourceKPTranslateGenuineGramL2 K hζ T u hu t ht := by
  simp only [sourceKPTranslateGenuineGramL2, adjoint_comp, adjoint_adjoint]

theorem sourceKPTranslateScalarGramL2_diag (t : Gf) (ht : J ≤ D t) :
    sourceKPTranslateScalarGramL2 K hζ T t ht t ht =
      ((J).relIndex (D t) : ℂ) • ContinuousLinearMap.id ℂ LY := by
  simpa only [Complex.ofReal_natCast, sourceKPTranslateScalarGramL2] using
    adjoint_comp_of_norm_sq (sourceKPTranslateCompactPullbackL2 K hζ T t ht)
      ((J).relIndex (D t) : ℝ) (sourceKPTranslateCompactPullbackL2_norm_sq K hζ T t ht)

theorem sourceKPTranslateGenuineGramL2_diag (t : Gf) (ht : J ≤ D t) :
    sourceKPTranslateGenuineGramL2 K hζ T t ht t ht =
      ((J).relIndex (D t) : ℂ) • ContinuousLinearMap.id ℂ H := by
  simpa only [Complex.ofReal_natCast, sourceKPTranslateGenuineGramL2] using
    adjoint_comp_of_norm_sq (sourceKPTranslateGenuinePullbackL2 K hζ T t ht)
      ((J).relIndex (D t) : ℝ) (sourceKPTranslateGenuinePullbackL2_norm_sq K hζ T t ht)

end
end ArtinMatthews
