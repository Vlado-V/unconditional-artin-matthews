module

public import ArtinMatthews.SourceKPTranslateH1Gram
public import ArtinMatthews.SourceHilbertPencil
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

/-! The actual genuine Hecke Gram operators preserve the native spectral pencil
and its nullspaces. -/
namespace ArtinMatthews
open NumberField ContinuousLinearMap
open scoped NumberField MatrixGroups AdeleRing
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
variable (T : Finset (SourceKPFiniteAdeleProjective K hζ))
include T

local notation "Gf" => SourceKPFiniteAdeleProjective K hζ
local notation "D" => sourceKPFiniteLevelConjugate K hζ
local notation "J" => sourceKPFiniteTranslateLevel K hζ T
local notation "H" => SourceKPGenuineAutomorphicL2 K hζ
local notation "V" => SourceKPCompactGenuineH1 K hζ
local notation "j" => sourceKPCompactGenuineH1Mass K hζ
local notation "S" => ContinuousLinearMap.comp (ContinuousLinearMap.adjoint j) j
local notation "A[" t ", " ht ", " u ", " hu "]" =>
  sourceKPTranslateGenuineGramH1 K hζ T t ht u hu
local notation "B[" t ", " ht ", " u ", " hu "]" =>
  sourceKPTranslateGenuineGramL2 K hζ T t ht u hu

theorem sourceKPTranslateGenuineGramH1_commutes_massGram (t : Gf) (ht : J ≤ D t)
    (u : Gf) (hu : J ≤ D u) :
    (S).comp A[t, ht, u, hu] = (A[t, ht, u, hu]).comp S := by
  let A := A[t, ht, u, hu]
  let B := B[t, ht, u, hu]
  have h : (j).comp A = B.comp j :=
    ContinuousLinearMap.ext (sourceKPTranslateGenuineGramH1_mass K hζ T t ht u hu)
  have hrev : (j).comp A[u, hu, t, ht] = (B[u, hu, t, ht]).comp j :=
    ContinuousLinearMap.ext (sourceKPTranslateGenuineGramH1_mass K hζ T u hu t ht)
  have hstar := congrArg (fun f : V →L[ℂ] H => f.adjoint) hrev
  simp only [ContinuousLinearMap.adjoint_comp, sourceKPTranslateGenuineGramH1_adjoint,
    sourceKPTranslateGenuineGramL2_adjoint] at hstar
  change A.comp (j).adjoint = (j).adjoint.comp B at hstar
  calc
    (S).comp A = (j).adjoint.comp ((j).comp A) := comp_assoc _ _ _
    _ = (j).adjoint.comp (B.comp j) := congrArg ((j).adjoint.comp ·) h
    _ = ((j).adjoint.comp B).comp j := (comp_assoc _ _ _).symm
    _ = (A.comp (j).adjoint).comp j := congrArg (fun f => f.comp j) hstar.symm
    _ = A.comp S := comp_assoc _ _ _

theorem sourceKPTranslateGenuineGramH1_commutes_pencil (t : Gf) (ht : J ≤ D t)
    (u : Gf) (hu : J ≤ D u) (z : ℂ) :
    (HilbertResolvent.pencil S z).comp A[t, ht, u, hu] =
      (A[t, ht, u, hu]).comp (HilbertResolvent.pencil S z) := by
  let A := A[t, ht, u, hu]
  apply ContinuousLinearMap.ext
  intro f
  have h := congrArg (fun R : V →L[ℂ] V => R f)
    (sourceKPTranslateGenuineGramH1_commutes_massGram K hζ T t ht u hu)
  change S (A f) = A (S f) at h
  change A f - (z+1) • S (A f) = A (f - (z+1) • S f)
  rw [h, map_sub, map_smul]

theorem sourceKPTranslateGenuineGramH1_mem_nullSpace (t : Gf) (ht : J ≤ D t)
    (u : Gf) (hu : J ≤ D u) (s : ℝ) {f : V}
    (hf : f ∈ HilbertResolvent.nullSpace S s) :
    A[t, ht, u, hu] f ∈ HilbertResolvent.nullSpace S s := by
  let A := A[t, ht, u, hu]
  let P := HilbertResolvent.pencil S (s : ℂ)
  change P f = 0 at hf
  change P (A f) = 0
  have h := congrArg (fun R : V →L[ℂ] V => R f)
    (sourceKPTranslateGenuineGramH1_commutes_pencil K hζ T t ht u hu (s : ℂ))
  change P (A f) = A (P f) at h
  rw [h, hf, map_zero]

end
end ArtinMatthews
