module

public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.Topology.Separation.CompletelyRegular
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Topology.Sheaves.Init
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Analysis.InnerProductSpace.Spectrum
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.InnerProductSpace.l2Space
public import Mathlib.NumberTheory.Chebyshev
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


set_option backward.privateInPublic true
@[expose] public section

/-! The independent compact Hilbert eigenbasis section, copied verbatim
from OAI/Analysis/CoulombIonization/FormDomain/CompactEigenbasis.lean.
Only the surrounding namespace/imports are specialized; the later coherent
state sections are independent and are not imported. -/

noncomputable section
namespace ArtinMatthews.SpectralCompact

open MeasureTheory Filter Module
open scoped BigOperators ComplexConjugate Topology

universe u
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def compactEigenspaceIndex (T : H →L[ℂ] H) (μ : ℂ) : Set (Module.End.eigenspace T.toLinearMap μ) :=
  (exists_hilbertBasis ℂ (Module.End.eigenspace T.toLinearMap μ)).choose

def compactEigenspaceBasis (T : H →L[ℂ] H) (μ : ℂ) :
    HilbertBasis (compactEigenspaceIndex T μ) ℂ (Module.End.eigenspace T.toLinearMap μ) :=
  (exists_hilbertBasis ℂ (Module.End.eigenspace T.toLinearMap μ)).choose_spec.choose

abbrev CompactSpectralIndex (T : H →L[ℂ] H) := Σ μ : ℂ, compactEigenspaceIndex T μ

def compactSpectralVector (T : H →L[ℂ] H) (i : CompactSpectralIndex T) : H :=
  compactEigenspaceBasis T i.1 i.2

lemma compactSpectralVector_eigen (T : H →L[ℂ] H) (i : CompactSpectralIndex T) :
    T (compactSpectralVector T i) = i.1 • compactSpectralVector T i :=
  Module.End.mem_eigenspace_iff.mp (compactEigenspaceBasis T i.1 i.2).property

lemma compactSpectralVector_orthonormal (T : H →L[ℂ] H) (hT : T.toLinearMap.IsSymmetric) :
    Orthonormal ℂ (compactSpectralVector T) :=
  hT.orthogonalFamily_eigenspaces.orthonormal_sigma_orthonormal
    (fun μ => (compactEigenspaceBasis T μ).orthonormal)

lemma compactSpectralVector_orthogonal_eq_bot (T : H →L[ℂ] H)
    (hTc : IsCompactOperator T) (hTs : T.toLinearMap.IsSymmetric) :
    (Submodule.span ℂ (Set.range (compactSpectralVector T)))ᗮ = ⊥ := by
  let S := Submodule.span ℂ (Set.range (compactSpectralVector T))
  have hs : (⨆ μ, Module.End.eigenspace T.toLinearMap μ) ≤ S.topologicalClosure := by
    apply iSup_le
    intro μ y hy
    let v : Module.End.eigenspace T.toLinearMap μ := ⟨y,hy⟩
    have hh := ((compactEigenspaceBasis T μ).hasSum_repr v).mapL
      (Module.End.eigenspace T.toLinearMap μ).subtypeL
    apply mem_closure_of_tendsto hh
    apply Eventually.of_forall
    intro s
    apply Submodule.sum_mem
    intro i _
    change ((compactEigenspaceBasis T μ).repr v i) • (compactSpectralVector T ⟨μ,i⟩) ∈ S
    exact S.smul_mem _ (Submodule.subset_span ⟨⟨μ,i⟩,rfl⟩)
  apply le_antisymm _ bot_le
  rw [← S.orthogonal_closure]
  exact (Submodule.orthogonal_le hs).trans
    (ContinuousLinearMap.orthogonalComplement_iSup_eigenspaces_eq_bot hTc hTs).le

def compactSpectralBasis (T : H →L[ℂ] H)
    (hTc : IsCompactOperator T) (hTs : T.toLinearMap.IsSymmetric) :
    HilbertBasis (CompactSpectralIndex T) ℂ H :=
  HilbertBasis.mkOfOrthogonalEqBot (compactSpectralVector_orthonormal T hTs)
    (compactSpectralVector_orthogonal_eq_bot T hTc hTs)

lemma compactSpectralBasis_apply (T : H →L[ℂ] H)
    (hTc : IsCompactOperator T) (hTs : T.toLinearMap.IsSymmetric)
    (i : CompactSpectralIndex T) : compactSpectralBasis T hTc hTs i = compactSpectralVector T i := by
  rw [compactSpectralBasis,HilbertBasis.coe_mkOfOrthogonalEqBot]

lemma compactSpectralBasis_eigen (T : H →L[ℂ] H)
    (hTc : IsCompactOperator T) (hTs : T.toLinearMap.IsSymmetric)
    (i : CompactSpectralIndex T) :
    T (compactSpectralBasis T hTc hTs i) = i.1 • compactSpectralBasis T hTc hTs i := by
  simp only [compactSpectralBasis_apply,compactSpectralVector_eigen]

end ArtinMatthews.SpectralCompact
