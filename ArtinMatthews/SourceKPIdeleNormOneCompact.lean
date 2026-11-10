module

public import ArtinMatthews.SourceKPCFTIdeleBridge
public import ClassFieldTheory.AlgebraicNumberTheory.Idele.NormOneCompact
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

/-! Actual compact representatives for norm-one ideles modulo principal ideles. -/

set_option relaxedAutoImplicit false

namespace ArtinMatthews
open NumberField IsDedekindDomain Topology
open scoped NumberField AdeleRing
noncomputable section

variable (K : Type) [Field K] [NumberField K]

def sourceKPIdeleNormOneCompact : Set (NumberField.IdeleGroup (𝓞 K) K) :=
  sourceKPCFTIdeleEquiv K '' _root_.IdeleGroup.compactNormOneClassCover (K := K)

lemma sourceKPIdeleNormOneCompact_isCompact : IsCompact (sourceKPIdeleNormOneCompact K) :=
  (_root_.IdeleGroup.isCompact_compactNormOneClassCover (K := K)).image
    (sourceKPCFTIdeleEquiv_continuous K)

lemma sourceKPIdeleNormOneCompact_norm (a : NumberField.IdeleGroup (𝓞 K) K)
    (ha : a ∈ sourceKPIdeleNormOneCompact K) : sourceKPIdeleAbsoluteNorm K a = 1 := by
  obtain ⟨b, hb, rfl⟩ := ha
  have hn := _root_.IdeleGroup.compactNormOneClassCover_subset_normOne hb
  change _root_.IdeleGroup.absoluteNorm b = 1 at hn
  rw [sourceKPCFTIdeleEquiv_norm, hn]
  simp

lemma sourceKPIdeleNormOneCompact_representative (a : NumberField.IdeleGroup (𝓞 K) K)
    (ha : sourceKPIdeleAbsoluteNorm K a = 1) :
    ∃ q : Kˣ, a * NumberField.IdeleGroup.unitEmbedding (𝓞 K) K q ∈ sourceKPIdeleNormOneCompact K := by
  let b := (sourceKPCFTIdeleEquiv K).symm a
  have hba : sourceKPCFTIdeleEquiv K b = a := (sourceKPCFTIdeleEquiv K).apply_symm_apply a
  have hb : b ∈ _root_.IdeleGroup.normOneSubgroup (K := K) := by
    change _root_.IdeleGroup.absoluteNorm b = 1
    apply Units.ext
    apply NNReal.eq
    have hn := sourceKPCFTIdeleEquiv_norm K b
    rw [hba, ha] at hn
    exact inv_eq_one.mp hn.symm
  have hclass : (QuotientGroup.mk' (_root_.IdeleGroup.principalSubgroup K) b) ∈
      (QuotientGroup.mk' (_root_.IdeleGroup.principalSubgroup K)) ''
        _root_.IdeleGroup.compactNormOneClassCover (K := K) := by
    rw [_root_.IdeleClassGroup.image_compactNormOneClassCover]
    exact (_root_.IdeleClassGroup.mk_mem_normOneSubgroup_iff b).mpr hb
  obtain ⟨c, hc, hcb⟩ := hclass
  have hprincipal : c / b ∈ _root_.IdeleGroup.principalSubgroup K :=
    QuotientGroup.eq_iff_div_mem.mp hcb
  obtain ⟨q, hq⟩ := hprincipal
  have he : b * _root_.IdeleGroup.principalIdele K q = c := by
    rw [hq, div_eq_mul_inv]
    simp
  refine ⟨q, ?_⟩
  have hrep : a * NumberField.IdeleGroup.unitEmbedding (𝓞 K) K q = sourceKPCFTIdeleEquiv K c := by
    rw [← hba, ← sourceKPCFTIdeleEquiv_principal, ← map_mul, he]
  rw [hrep]
  exact ⟨c, hc, rfl⟩

theorem sourceKPIdeleNormOne_compact_representatives :
    ∃ C : Set (NumberField.IdeleGroup (𝓞 K) K), IsCompact C ∧
      (∀ a ∈ C, sourceKPIdeleAbsoluteNorm K a = 1) ∧
      ∀ a : NumberField.IdeleGroup (𝓞 K) K, sourceKPIdeleAbsoluteNorm K a = 1 →
        ∃ q : Kˣ, a * NumberField.IdeleGroup.unitEmbedding (𝓞 K) K q ∈ C :=
  ⟨sourceKPIdeleNormOneCompact K, sourceKPIdeleNormOneCompact_isCompact K,
    sourceKPIdeleNormOneCompact_norm K, sourceKPIdeleNormOneCompact_representative K⟩

end
end ArtinMatthews
