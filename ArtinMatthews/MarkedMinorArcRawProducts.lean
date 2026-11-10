module

public import ArtinMatthews.MarkedMinorArcRawCleanKernel
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

/-! Actual ordered prime-slot products and the physical squarefree copied
product, retaining the source disjoint bands and full-list distinctness. -/
namespace ArtinMatthews
open scoped BigOperators

/-- Forget only the primality proof, preserving the exact numeric band. -/
def markedRawNaturalBand (P : Finset Nat.Primes) : Finset ℕ := P.image (fun p : Nat.Primes => (p : ℕ))

theorem markedRawNaturalBand_prime (P : Finset Nat.Primes) {p : ℕ}
    (hp : p ∈ markedRawNaturalBand P) : p.Prime := by
  obtain ⟨q,_,rfl⟩ := Finset.mem_image.mp hp
  exact q.2

theorem markedRawNaturalBand_disjoint {J : Type*} (P : J → Finset Nat.Primes)
    (hP : Pairwise (fun i j => Disjoint (P i) (P j))) :
    Pairwise (fun i j => Disjoint (markedRawNaturalBand (P i)) (markedRawNaturalBand (P j))) := by
  intro i j hij
  apply Finset.disjoint_left.mpr
  intro p hpi hpj
  obtain ⟨a,ha,hap⟩ := Finset.mem_image.mp hpi
  obtain ⟨b,hb,hbp⟩ := Finset.mem_image.mp hpj
  have he : a=b := Subtype.ext (hap.trans hbp.symm)
  exact Finset.disjoint_left.mp (hP hij) ha (he ▸ hb)

/-- Every one-prime-per-disjoint-band tuple is determined by its actual
integer product, before any measure or operator estimate is applied. -/
theorem markedRawLastProduct_injective {J : Type*} [Fintype J]
    (P : J → Finset Nat.Primes) (hP : Pairwise (fun i j => Disjoint (P i) (P j))) :
    Function.Injective (markedRawLastProduct (P := P)) := by
  intro a b hab
  have he := marked_disjoint_prime_tuple_eq_of_product_eq (fun j => markedRawNaturalBand (P j))
    (fun j _ hp => markedRawNaturalBand_prime (P j) hp) (markedRawNaturalBand_disjoint P hP)
    (fun j => ((a j).1 : ℕ)) (fun j => ((b j).1 : ℕ))
    (fun j => Finset.mem_image.mpr ⟨(a j).1,(a j).2,rfl⟩)
    (fun j => Finset.mem_image.mpr ⟨(b j).1,(b j).2,rfl⟩) hab
  funext j
  exact Subtype.ext (Subtype.ext (congrFun he j))

theorem markedRawProductMap_injective {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} (hP : Pairwise (fun i j => Disjoint (P i) (P j)))
    {Z : Finset (ℤ × ℤ)} : Function.Injective (markedRawProductMap (P := P) (Z := Z)) := by
  intro u v huv
  have hz := congrArg Prod.fst huv
  have hp := congrArg (fun a => a.2.1) huv
  change (markedRawLastProduct u.2 : ℤ)=(markedRawLastProduct v.2 : ℤ) at hp
  have hl : markedRawLastProduct u.2=markedRawLastProduct v.2 := by exact_mod_cast hp
  exact Prod.ext hz (markedRawLastProduct_injective P hP hl)

/-- Actual copied slots in disjoint bands are globally distinct whenever
each copied list is distinct. -/
theorem markedRawCopiedValues_injective {J : Type*} [Fintype J]
    {P : J → Finset Nat.Primes} (hP : Pairwise (fun i j => Disjoint (P i) (P j)))
    {pads : ℕ} (a : MarkedRawActive P pads) (ha : ∀ j, Function.Injective (a j)) :
    Function.Injective (fun jk : J × Fin pads => ((a jk.1 jk.2).1 : ℕ)) := by
  rintro ⟨j,k⟩ ⟨i,l⟩ he
  by_cases hji : j=i
  · subst i
    exact Prod.ext rfl (ha j (Subtype.ext (Subtype.ext he)))
  · have he' : (a j k).1=(a i l).1 := Subtype.ext he
    have hmem : (a j k).1 ∈ P i := by rw [he']; exact (a i l).2
    exact False.elim (Finset.disjoint_left.mp (hP hji) (a j k).2 hmem)

/-- The shared copied product is squarefree as a consequence of the actual
physical list restriction; it is not an extra raw-operator support premise. -/
theorem markedRawCopiedProduct_squarefree {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} (hP : Pairwise (fun i j => Disjoint (P i) (P j)))
    {pads : ℕ} (a : MarkedRawActive P pads) (ha : ∀ j, Function.Injective (a j)) :
    Squarefree (markedRawCopiedProduct a) := by
  classical
  let f : J × Fin pads → ℕ := fun jk => (a jk.1 jk.2).1
  let T := Finset.univ.image f
  have hprime : ∀ p ∈ T, p.Prime := by
    intro p hp
    obtain ⟨jk,_,rfl⟩ := Finset.mem_image.mp hp
    exact (a jk.1 jk.2).1.2
  have hs : Squarefree (∏ p ∈ T, p) := by
    apply Finset.squarefree_prod_of_pairwise_isCoprime
    · intro p hp q hq hpq
      exact Nat.coprime_iff_isRelPrime.mp ((Nat.coprime_primes (hprime p hp) (hprime q hq)).mpr hpq)
    · exact fun p hp => (hprime p hp).squarefree
  have hinj := markedRawCopiedValues_injective hP a ha
  rw [Finset.prod_image (fun _ _ _ _ he => hinj he)] at hs
  simpa only [markedRawCopiedProduct,f,Fintype.prod_prod_type] using hs

theorem markedRawCopiedProduct_squarefree_of_fullDistinct {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} (hP : Pairwise (fun i j => Disjoint (P i) (P j)))
    (pads : ℕ) (a : MarkedRawActive P (pads+1)) (ha : MarkedRawActiveDistinct a) :
    Squarefree (markedRawCopiedProduct ((markedRawActiveSplit pads) a).1) := by
  apply markedRawCopiedProduct_squarefree hP
  intro j
  exact (ha j).comp (Fin.castSucc_injective pads)

end ArtinMatthews
