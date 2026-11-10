module

public import ArtinMatthews.MarkedMinorArcDirtyAnchor
public import ArtinMatthews.MarkedMinorArcRawGoodFirst
public import ArtinMatthews.MarkedTypeIIGoodSecond
public import ArtinMatthews.MarkedMinorArcDirtyChargedOmissions
public import ArtinMatthews.MarkedMinorArcDirtyTargetAnchor
public import ArtinMatthews.MarkedMinorArcRawProducts
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
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! Literal dirty target choices, retaining the actual determinant and
actual indexed projective hit. The numeric omission/Z projection is unique
on a good fresh draw; target positions retain their true multiplicity. -/
noncomputable section
namespace ArtinMatthews

open scoped BigOperators

def markedRawDirtyTargetChoices {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} {M : ℕ} (source : MarkedRawActive P M)
    {Pstar : Finset Nat.Primes} (a : MarkedRawParticle Pstar)
    (Zs : Finset ℕ) (V : Finset (ℤ × ℤ)) (hV : ∀ v ∈ V, IsCoprime v.1 v.2)
    (z : ℤ × ℤ) (T : ℤ) (Q : Finset ℤ) :
    Finset (((J → Fin M) × ℕ) × V) := by
  classical
  exact ((Finset.univ.product Zs).product Finset.univ).filter (fun c =>
    (∀ j k, ¬markedRawNumericActive source j k ∣ c.1.2) ∧
    ((markedSourceCopiedProduct (markedRawNumericActive source) c.1.1*c.1.2:ℕ):ℤ) ∈ Q ∧
    markedMinorIntegerDet z c.2.1=markedMinorDirtyDeterminant
      (markedSourceFullProduct (markedRawNumericActive source):ℤ)
      (markedSourceCopiedProduct (markedRawNumericActive source) c.1.1:ℤ) (a.1.1:ℕ) (c.1.2:ℤ) T ∧
    MarkedRawParticleHits Pstar c.2.1 (hV _ c.2.2) a)

theorem markedRawDirtyTargetChoices_numeric_unique {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} {M : ℕ} (source : MarkedRawActive P M)
    (hdis : Pairwise (fun i j => Disjoint (P i) (P j))) (hdist : ∀ j, Function.Injective (source j))
    {Pstar : Finset Nat.Primes} (a : MarkedRawParticle Pstar)
    (hban : ∀ j k, (source j k).1 ≠ a.1.1)
    (Zs : Finset ℕ) (V : Finset (ℤ × ℤ)) (hV : ∀ v ∈ V, IsCoprime v.1 v.2)
    (z w : ℤ × ℤ) (T : ℤ) (Q : Finset ℤ) (r : ℝ)
    (hd : markedMinorIntegerDet z w=1) (hz : markedMinorIntegerTau r z ≠ 0)
    (hbox : ∀ v ∈ V, |markedMinorIntegerTau r v/markedMinorIntegerTau r z| ≤ 16)
    {ε : ℝ} (hε : 0 < ε) (hp : 1/(a.1.1:ℕ) ≤ ε)
    (hg : ((markedMinorIntegerTau r w/markedMinorIntegerTau r z:ℝ):AddCircle (1:ℝ)) ∉
      markedPairBadRoots Q T (100*ε))
    (c d : ((J → Fin M) × ℕ) × V)
    (hc : c ∈ markedRawDirtyTargetChoices source a Zs V hV z T Q)
    (hdd : d ∈ markedRawDirtyTargetChoices source a Zs V hV z T Q) : c.1=d.1 := by
  classical
  obtain ⟨hbanC,hQC,hjC,hhitC⟩ := (Finset.mem_filter.mp hc).2
  obtain ⟨hbanD,hQD,hjD,hhitD⟩ := (Finset.mem_filter.mp hdd).2
  let R : ℝ := markedMinorIntegerTau r w/markedMinorIntegerTau r z
  let A : ℝ := (((markedSourceFullProduct (markedRawNumericActive source):ℤ):ℝ)*R+
    markedMinorIntegerDet c.2.1 w)/(a.1.1:ℕ)
  have hres := markedRawDirty_target_anchor_residue_unique source a hban
    (markedSourceCopiedProduct (markedRawNumericActive source) c.1.1:ℤ)
    (markedSourceCopiedProduct (markedRawNumericActive source) d.1.1:ℤ)
    (c.1.2:ℤ) (d.1.2:ℤ) T T z w c.2.1 d.2.1 hd (hV _ c.2.2) (hV _ d.2.2) hjC hjD hhitC hhitD
  have hmod : Int.ModEq ((a.1.1:ℕ):ℤ) (markedMinorIntegerDet d.2.1 w) (markedMinorIntegerDet c.2.1 w) :=
    (ZMod.intCast_eq_intCast_iff _ _ _).mp hres.symm
  have hcprox := markedRawDirty_target_anchor_proximity source a
    (markedSourceCopiedProduct (markedRawNumericActive source) c.1.1:ℤ) (c.1.2:ℤ) T
    (markedMinorIntegerDet c.2.1 w) z w c.2.1 r hd hz hjC (Int.ModEq.refl _) (hbox _ c.2.2)
  have hdprox := markedRawDirty_target_anchor_proximity source a
    (markedSourceCopiedProduct (markedRawNumericActive source) d.1.1:ℤ) (d.1.2:ℤ) T
    (markedMinorIntegerDet c.2.1 w) z w d.2.1 r hd hz hjD hmod (hbox _ d.2.2)
  have hcircle (D Z : ℕ) :
      ((((D*Z:ℕ):ℤ)*T) • (R:AddCircle (1:ℝ))-(A:AddCircle (1:ℝ))) =
        (((D:ℝ)*Z*T*R-A:ℝ):AddCircle (1:ℝ)) := by
    rw [← AddCircle.coe_zsmul,← AddCircle.coe_sub,zsmul_eq_mul]
    congr 1
    push_cast
    ring
  have hcmem : ((markedSourceCopiedProduct (markedRawNumericActive source) c.1.1*c.1.2:ℕ):ℤ) ∈
      markedMinorDirtyAnchorTrials Q T (R:AddCircle (1:ℝ)) (A:AddCircle (1:ℝ)) (a.1.1:ℕ) := by
    apply Finset.mem_filter.mpr
    refine ⟨hQC,?_⟩
    rw [hcircle]
    exact hcprox
  have hdmem : ((markedSourceCopiedProduct (markedRawNumericActive source) d.1.1*d.1.2:ℕ):ℤ) ∈
      markedMinorDirtyAnchorTrials Q T (R:AddCircle (1:ℝ)) (A:AddCircle (1:ℝ)) (a.1.1:ℕ) := by
    apply Finset.mem_filter.mpr
    refine ⟨hQD,?_⟩
    rw [hcircle]
    exact hdprox
  have hsource : ∀ j k, markedRawNumericActive source j k ∈ markedRawNaturalBand (P j) :=
    fun j k => Finset.mem_image.mpr ⟨(source j k).1,(source j k).2,rfl⟩
  have hdistNat : ∀ j, Function.Injective (markedRawNumericActive source j) := by
    intro j u v huv
    exact hdist j (Subtype.ext (Subtype.ext huv))
  have hcard := markedDirtyNumericChoices_card_le_one (fun j => markedRawNaturalBand (P j))
    (fun j _ hp => markedRawNaturalBand_prime (P j) hp) (markedRawNaturalBand_disjoint P hdis)
    (markedRawNumericActive source) hsource hdistNat Zs Q T (R:AddCircle (1:ℝ)) (A:AddCircle (1:ℝ)) hε hp hg
  apply (Finset.card_le_one.mp hcard) c.1 ?_ d.1 ?_
  · exact Finset.mem_filter.mpr ⟨(Finset.mem_product.mp (Finset.mem_filter.mp hc).1).1,hbanC,hcmem⟩
  · exact Finset.mem_filter.mpr ⟨(Finset.mem_product.mp (Finset.mem_filter.mp hdd).1).1,hbanD,hdmem⟩

end ArtinMatthews
