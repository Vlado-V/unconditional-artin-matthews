module

/- Adapted in the Artin–Matthews source bundle. The source, upstream and packaged digests are recorded in SOURCE_MANIFEST.json. -/

public import OAI.RepresentationTheory.Weil.AdelicSplitting.FiniteLattices
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
public import OAI.RepresentationTheory.Weil.AdelicSplitting.StrongApproximation


set_option backward.privateInPublic true
@[expose] public section

/-! # Finite Cosets -/

namespace OAI.RepresentationTheory.Weil.AdelicSplitting.FiniteCosets.Construction

noncomputable section

/-! Compactly supported finite-adelic functions with an integral lattice
of periods expand into finitely many actual rational lattice cosets. -/

open scoped Classical _root_.NumberField

variable {F : Type} [Field F] [NumberField F] {ι : Type*} [Fintype ι]

def finiteRationalPosition (a : ι → F) : ι → ArchimedeanAdeles.Construction.FiniteAdeles F :=
  fun i => algebraMap F (ArchimedeanAdeles.Construction.FiniteAdeles F) (a i)

def finitePositionIndicator (q : F) (hq : q ≠ 0) (x : ι → ArchimedeanAdeles.Construction.FiniteAdeles F) : ℂ :=
  (FiniteLattices.Construction.finiteAdelicPositionLattice (ι := ι) q hq : Set (ι → ArchimedeanAdeles.Construction.FiniteAdeles F)).indicator (fun _ => 1) x

def finitePositionCosetIndicator (q : F) (hq : q ≠ 0) (a x : ι → ArchimedeanAdeles.Construction.FiniteAdeles F) : ℂ :=
  finitePositionIndicator q hq (x - a)

omit [Fintype ι] in
theorem denseRange_finiteRationalPosition : DenseRange (finiteRationalPosition (F := F) (ι := ι)) :=
  DenseRange.piMap (fun _ : ι => StrongApproximation.Construction.denseRange_rational_finiteAdeles F)

theorem finiteAdelicPositionLattice_rational_coset (q : F) (hq : q ≠ 0) (x : ι → ArchimedeanAdeles.Construction.FiniteAdeles F) :
    ∃ a : ι → F, x - finiteRationalPosition a ∈ FiniteLattices.Construction.finiteAdelicPositionLattice q hq := by
  exact (denseRange_finiteRationalPosition (F := F) (ι := ι)).exists_mem_open
    (s := {y : ι → ArchimedeanAdeles.Construction.FiniteAdeles F | x - y ∈ FiniteLattices.Construction.finiteAdelicPositionLattice q hq})
    ((FiniteLattices.Construction.finiteAdelicPositionLattice_isOpen q hq).preimage (continuous_const.sub continuous_id))
    ⟨x, by simp⟩

abbrev FinitePositionQuotient (q : F) (hq : q ≠ 0) := (ι → ArchimedeanAdeles.Construction.FiniteAdeles F) ⧸ FiniteLattices.Construction.finiteAdelicPositionLattice q hq

def rationalPositionQuotientMap (q : F) (hq : q ≠ 0) (a : ι → F) : FinitePositionQuotient (ι := ι) q hq :=
  QuotientAddGroup.mk (finiteRationalPosition a)

theorem rationalPositionQuotientMap_surjective (q : F) (hq : q ≠ 0) :
    Function.Surjective (rationalPositionQuotientMap (ι := ι) q hq) := by
  intro c
  obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective c
  obtain ⟨a, ha⟩ := finiteAdelicPositionLattice_rational_coset q hq x
  refine ⟨a, ?_⟩
  symm
  exact QuotientAddGroup.eq_iff_sub_mem.mpr ha

def finitePositionQuotientRep (q : F) (hq : q ≠ 0) (c : FinitePositionQuotient (ι := ι) q hq) : ι → F :=
  (rationalPositionQuotientMap_surjective q hq c).choose

theorem finitePositionQuotientRep_covers (q : F) (hq : q ≠ 0) (c : FinitePositionQuotient (ι := ι) q hq) :
    (QuotientAddGroup.mk (finiteRationalPosition (finitePositionQuotientRep q hq c)) : FinitePositionQuotient q hq) = c :=
  (rationalPositionQuotientMap_surjective q hq c).choose_spec

theorem finitePositionCosetIndicator_quotient (q : F) (hq : q ≠ 0)
    (c : FinitePositionQuotient (ι := ι) q hq) (x : ι → ArchimedeanAdeles.Construction.FiniteAdeles F) :
    finitePositionCosetIndicator q hq (finiteRationalPosition (finitePositionQuotientRep q hq c)) x =
      if (QuotientAddGroup.mk x : FinitePositionQuotient q hq) = c then 1 else 0 := by
  have hmem : x - finiteRationalPosition (finitePositionQuotientRep q hq c) ∈ FiniteLattices.Construction.finiteAdelicPositionLattice q hq ↔
      (QuotientAddGroup.mk x : FinitePositionQuotient q hq) = c := by
    rw [← QuotientAddGroup.eq_iff_sub_mem, finitePositionQuotientRep_covers]
  simp only [finitePositionCosetIndicator, finitePositionIndicator, Set.indicator, SetLike.mem_coe, hmem]

theorem finite_function_coset_expansion (f : (ι → ArchimedeanAdeles.Construction.FiniteAdeles F) → ℂ) (hf : HasCompactSupport f) (q : F) (hq : q ≠ 0)
    (hp : ∀ u ∈ FiniteLattices.Construction.finiteAdelicPositionLattice q hq, ∀ x, f (u + x) = f x) :
    ∃ s : Finset (FinitePositionQuotient (ι := ι) q hq), ∀ x : ι → ArchimedeanAdeles.Construction.FiniteAdeles F,
      f x = ∑ c ∈ s, f (finiteRationalPosition (finitePositionQuotientRep q hq c)) *
        finitePositionCosetIndicator q hq (finiteRationalPosition (finitePositionQuotientRep q hq c)) x := by
  let : DiscreteTopology (FinitePositionQuotient (ι := ι) q hq) :=
    QuotientAddGroup.discreteTopology (FiniteLattices.Construction.finiteAdelicPositionLattice_isOpen q hq)
  let Q : (ι → ArchimedeanAdeles.Construction.FiniteAdeles F) → FinitePositionQuotient q hq := QuotientAddGroup.mk
  have hcompact := hf.image
    (QuotientAddGroup.continuous_mk : Continuous Q)
  let s := hcompact.finite_of_discrete.toFinset
  have hcoeff (x : ι → ArchimedeanAdeles.Construction.FiniteAdeles F) : f (finiteRationalPosition (finitePositionQuotientRep q hq (Q x))) = f x := by
    have hdiff : finiteRationalPosition (finitePositionQuotientRep q hq (Q x)) - x ∈ FiniteLattices.Construction.finiteAdelicPositionLattice q hq :=
      QuotientAddGroup.eq_iff_sub_mem.mp (finitePositionQuotientRep_covers q hq (Q x))
    simpa only [sub_add_cancel] using hp _ hdiff x
  refine ⟨s, fun x => ?_⟩
  symm
  rw [Finset.sum_eq_single (Q x)]
  · rw [finitePositionCosetIndicator_quotient, ite_eq_left rfl, mul_one, hcoeff]
  · intro c _ hc
    rw [finitePositionCosetIndicator_quotient, ite_eq_right (Ne.symm hc), mul_zero]
  · intro hx
    rw [finitePositionCosetIndicator_quotient, ite_eq_left rfl, mul_one, hcoeff]
    by_contra hφ
    apply hx
    apply (hcompact.finite_of_discrete.mem_toFinset).mpr
    exact ⟨x, subset_tsupport f hφ, rfl⟩

end

end OAI.RepresentationTheory.Weil.AdelicSplitting.FiniteCosets.Construction
