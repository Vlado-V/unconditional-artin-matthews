module

public import ArtinMatthews.SourceKPCuspFiniteIdeal
public import ArtinMatthews.SourceKPMinkowskiCuspTorus
public import OAI.RepresentationTheory.Weil.AdelicSplitting.ArchimedeanCharacterLattice
public import ArtinMatthews.SourceAdelicRationalTopology
public import ArtinMatthews.SourceKPFiniteCuspPeriod
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
public import Mathlib.Topology.Algebra.ProperAction.Basic
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! The exact additive principal cusp quotient and its scaled Minkowski coordinates. -/

set_option relaxedAutoImplicit false

namespace ArtinMatthews
open NumberField IsDedekindDomain Module Module.Free Topology
open OAI.RepresentationTheory.Weil.AdelicSplitting
open scoped NumberField AdeleRing Classical
noncomputable section

variable (K : Type) [Field K] [NumberField K] (d : 𝓞 K)
local notation "E" => mixedEmbedding.mixedSpace K

def sourceKPCuspPrincipalPeriods : AddSubgroup 𝔸[K] :=
  sourceKPAdelicRationals K ⊔ (sourceKPCuspFiniteIdeal K d).map (sourceKPFiniteAddEmbedding K)

abbrev SourceKPCuspPrincipalQuotient := 𝔸[K] ⧸ sourceKPCuspPrincipalPeriods K d

def sourceKPCuspArchQuotientMap : E →+ SourceKPCuspPrincipalQuotient K d :=
  (QuotientAddGroup.mk' (sourceKPCuspPrincipalPeriods K d)).comp
    (ArchimedeanCharacterLattice.Construction.mixedAdelicAdd K)

variable (hd : d ≠ 0)

lemma sourceKPCuspArchQuotientMap_ker :
    (sourceKPCuspArchQuotientMap K d).ker = (sourceKPCuspLattice K d hd).toAddSubgroup := by
  apply AddSubgroup.ext
  intro x
  change ((ArchimedeanCharacterLattice.Construction.mixedAdelicAdd K x : 𝔸[K]) :
    SourceKPCuspPrincipalQuotient K d) = 0 ↔ x ∈ sourceKPCuspLattice K d hd
  rw [QuotientAddGroup.eq_zero_iff, sourceKPCuspPrincipalPeriods, AddSubgroup.mem_sup,
    sourceKPCuspLattice_mem]
  constructor
  · rintro ⟨y, ⟨q, rfl⟩, z, ⟨t, ht, rfl⟩, he⟩
    have hfin : algebraMap K 𝔸ᶠ[K] q + t = 0 := congrArg Prod.snd he
    have hq : algebraMap K 𝔸ᶠ[K] q ∈ sourceKPCuspFiniteIdeal K d := by
      rw [eq_neg_of_add_eq_zero_left hfin]
      exact (sourceKPCuspFiniteIdeal K d).neg_mem ht
    obtain ⟨r, hr⟩ := (sourceKPCuspFiniteIdeal_rational K d hd q).mp hq
    have harch : algebraMap K (InfiniteAdeleRing K) q =
        (InfiniteAdeleRing.ringEquiv_mixedSpace K).symm x := by
      have hh := congrArg Prod.fst he
      change algebraMap K (InfiniteAdeleRing K) q + 0 =
        (InfiniteAdeleRing.ringEquiv_mixedSpace K).symm x at hh
      simpa only [add_zero] using hh
    have hx : mixedEmbedding K q = x := by
      have hh := congrArg (InfiniteAdeleRing.ringEquiv_mixedSpace K) harch
      simpa only [← InfiniteAdeleRing.mixedEmbedding_eq_algebraMap_comp,
        RingEquiv.apply_symm_apply] using hh
    exact ⟨r, by rw [show ((d*r : 𝓞 K) : K) = (d:K)*(r:K) from map_mul (algebraMap (𝓞 K) K) d r, hr]; exact hx⟩
  · rintro ⟨r, hr⟩
    let q : K := (d : K) * (r : K)
    have hq : algebraMap K 𝔸ᶠ[K] q ∈ sourceKPCuspFiniteIdeal K d :=
      (sourceKPCuspFiniteIdeal_rational K d hd q).mpr ⟨r, rfl⟩
    refine ⟨algebraMap K 𝔸[K] q, ⟨q, rfl⟩,
      sourceKPFiniteAddEmbedding K (-algebraMap K 𝔸ᶠ[K] q),
      ⟨_, (sourceKPCuspFiniteIdeal K d).neg_mem hq, rfl⟩, ?_⟩
    rw [← hr, ArchimedeanCharacterLattice.Construction.mixedAdelicAdd_rational]
    apply Prod.ext
    · exact add_zero _
    · exact add_neg_cancel _

include hd in
lemma sourceKPCuspArchQuotientMap_surjective : Function.Surjective (sourceKPCuspArchQuotientMap K d) := by
  intro z
  obtain ⟨a, rfl⟩ := QuotientAddGroup.mk_surjective z
  obtain ⟨q, hq⟩ := sourceKPCuspFiniteIdeal_remainder K d hd a.2
  let x : E := InfiniteAdeleRing.ringEquiv_mixedSpace K (a.1 - algebraMap K (InfiniteAdeleRing K) q)
  refine ⟨x, ?_⟩
  apply QuotientAddGroup.eq_iff_sub_mem.mpr
  suffices a - ArchimedeanCharacterLattice.Construction.mixedAdelicAdd K x ∈
      sourceKPCuspPrincipalPeriods K d by
    simpa only [neg_sub] using (sourceKPCuspPrincipalPeriods K d).neg_mem this
  apply AddSubgroup.mem_sup.mpr
  refine ⟨algebraMap K 𝔸[K] q, ⟨q,rfl⟩,
    sourceKPFiniteAddEmbedding K (a.2 - algebraMap K 𝔸ᶠ[K] q), ⟨_, hq, rfl⟩, ?_⟩
  apply Prod.ext
  · change algebraMap K (InfiniteAdeleRing K) q + 0 =
      a.1 - (InfiniteAdeleRing.ringEquiv_mixedSpace K).symm x
    rw [show (InfiniteAdeleRing.ringEquiv_mixedSpace K).symm x =
      a.1 - algebraMap K (InfiniteAdeleRing K) q from (InfiniteAdeleRing.ringEquiv_mixedSpace K).symm_apply_apply _]
    abel
  · change algebraMap K 𝔸ᶠ[K] q + (a.2 - algebraMap K 𝔸ᶠ[K] q) = a.2 - 0
    abel

lemma sourceKPCuspArchQuotientMap_continuous : Continuous (sourceKPCuspArchQuotientMap K d) :=
  QuotientAddGroup.continuous_mk.comp (ArchimedeanCharacterLattice.Construction.mixedAdelicAdd_continuous K)

def sourceKPCuspArchQuotientEquiv :
    (E ⧸ (sourceKPCuspLattice K d hd).toAddSubgroup) ≃+ SourceKPCuspPrincipalQuotient K d :=
  (QuotientAddGroup.quotientAddEquivOfEq (sourceKPCuspArchQuotientMap_ker K d hd).symm).trans
    (QuotientAddGroup.quotientKerEquivOfSurjective (sourceKPCuspArchQuotientMap K d)
      (sourceKPCuspArchQuotientMap_surjective K d hd))

lemma sourceKPCuspArchQuotientEquiv_mk (x : E) :
    sourceKPCuspArchQuotientEquiv K d hd (QuotientAddGroup.mk x) = sourceKPCuspArchQuotientMap K d x := rfl

include hd in
lemma sourceKPCuspArchQuotientMap_isOpenMap : IsOpenMap (sourceKPCuspArchQuotientMap K d) := by
  intro U hU
  let e := ArchimedeanAdeles.Construction.infiniteAdeleMixedHomeomorph K
  let V : Set 𝔸[K] := (e.symm '' U) ×ˢ (sourceKPCuspFiniteIdeal K d : Set 𝔸ᶠ[K])
  have hV : IsOpen V := (e.symm.isOpenMap U hU).prod (sourceKPCuspFiniteIdeal_isOpen K d hd)
  have he : sourceKPCuspArchQuotientMap K d '' U =
      (QuotientAddGroup.mk : 𝔸[K] → SourceKPCuspPrincipalQuotient K d) '' V := by
    ext z
    constructor
    · rintro ⟨x,hx,rfl⟩
      refine ⟨ArchimedeanCharacterLattice.Construction.mixedAdelicAdd K x, ?_, rfl⟩
      exact ⟨⟨x,hx,rfl⟩,(sourceKPCuspFiniteIdeal K d).zero_mem⟩
    · rintro ⟨a,⟨⟨x,hx,hxa⟩,ha⟩,rfl⟩
      refine ⟨x,hx,?_⟩
      apply QuotientAddGroup.eq_iff_sub_mem.mpr
      apply AddSubgroup.mem_sup_right
      refine ⟨-a.2,(sourceKPCuspFiniteIdeal K d).neg_mem ha,?_⟩
      apply Prod.ext
      · change 0 = e.symm x - a.1
        rw [hxa, sub_self]
      · change -a.2 = 0 - a.2
        simp
  rw [he]
  exact QuotientAddGroup.isOpenMap_coe V hV

lemma sourceKPCuspArchQuotientEquiv_continuous : Continuous (sourceKPCuspArchQuotientEquiv K d hd) := by
  apply (QuotientAddGroup.isQuotientMap_mk (sourceKPCuspLattice K d hd).toAddSubgroup).continuous_iff.mpr
  simpa only [Function.comp_def, sourceKPCuspArchQuotientEquiv_mk] using sourceKPCuspArchQuotientMap_continuous K d

lemma sourceKPCuspArchQuotientEquiv_isOpenMap : IsOpenMap (sourceKPCuspArchQuotientEquiv K d hd) := by
  apply IsOpenMap.of_comp QuotientAddGroup.continuous_mk QuotientAddGroup.mk_surjective
  simpa only [Function.comp_def, sourceKPCuspArchQuotientEquiv_mk] using sourceKPCuspArchQuotientMap_isOpenMap K d hd

def sourceKPCuspArchQuotientHomeomorph :
    (E ⧸ (sourceKPCuspLattice K d hd).toAddSubgroup) ≃ₜ+ SourceKPCuspPrincipalQuotient K d where
  __ := sourceKPCuspArchQuotientEquiv K d hd
  continuous_toFun := sourceKPCuspArchQuotientEquiv_continuous K d hd
  continuous_invFun := (sourceKPCuspArchQuotientEquiv K d hd).toEquiv.continuous_symm_iff.mpr
    (sourceKPCuspArchQuotientEquiv_isOpenMap K d hd)

def sourceKPCuspPrincipalTorusHomeomorph :
    SourceKPCuspPrincipalQuotient K d ≃ₜ+ UnitAddTorus (ChooseBasisIndex ℤ (𝓞 K)) :=
  (sourceKPCuspArchQuotientHomeomorph K d hd).symm.trans (sourceKPCuspTorusHomeomorph K d hd)

include hd in
lemma sourceKPCuspPrincipalQuotient_compact : CompactSpace (SourceKPCuspPrincipalQuotient K d) :=
  (sourceKPCuspPrincipalTorusHomeomorph K d hd).symm.toHomeomorph.compactSpace

include hd in
lemma sourceKPCuspPrincipalQuotient_t2 : T2Space (SourceKPCuspPrincipalQuotient K d) :=
  (sourceKPCuspPrincipalTorusHomeomorph K d hd).toHomeomorph.isEmbedding.t2Space

end
end ArtinMatthews
