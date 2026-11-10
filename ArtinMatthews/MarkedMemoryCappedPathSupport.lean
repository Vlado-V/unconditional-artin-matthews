module

public import ArtinMatthews.MarkedMemoryCappedPathConstruction
public import ArtinMatthews.MarkedMemoryIndependentMarks
public import ArtinMatthews.MarkedMemoryCappedPathIndependent
public import ArtinMatthews.MarkedMemoryIndependentAnchorConverse
public import ArtinMatthews.MarkedMemoryIndependentPrimeDistinct
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

/-! Compatible primewise choices at the literal pending capacity yield
actual anchor-admissible, birth-distinct histories. These support facts
are derived for every birth and copied-slot decoration. -/
namespace ArtinMatthews
noncomputable section
attribute [local instance] Classical.decEq Classical.propDecidable

variable {J : Type*} [Fintype J] {P : J → Finset Nat.Primes}
  {pads n B : ℕ} {Z : Finset (ℤ × ℤ)}
  (hZ : ∀ z∈Z,IsCoprime z.1 z.2) (d : MarkedMemoryActivePathData P pads Z n)
  (c : MarkedMemoryPathPrimeChoices (P := P) (n := n))
  (hc : MarkedMemoryPathChoicesCompatible d hZ c)
  (hcap : MarkedMemoryPathCapacity hZ d c hc B)
  (births : MarkedMemoryEndpointBirthOrders (markedMemoryPathEndpointData hZ d c hc))


theorem markedMemoryCappedPathIndependent_active_particle (v : Fin (n+1)) (j : J) (k : Fin (pads+1)) :
    (markedMemoryCappedPathIndependent (B := B) hZ d c hc hcap births).particle j
      ((markedMemoryCappedPathIndependent (B := B) hZ d c hc hcap births).activeId v.val j k)=
        markedRawAnchoredParticle (P j) (d.active v j k) (d.position v).1 (hZ _ (d.position v).2) := by
  let raw := markedMemoryCappedPathIndependent (B := B) hZ d c hc hcap births
  have hid := markedMemoryCappedPathIndependent_activeId (B := B) hZ d c hc hcap births v j k
  have hp := congrArg (raw.particle j) hid
  have hp2 := markedMemoryCappedPathIndependent_particle (B := B) hZ d c hc hcap births j
    (markedMemoryPathActiveUsed d c v j k)
  have hl := markedMemoryPrimeBirthVisit_active (markedMemoryPathPrimeLines hZ d (d.active v j k))
    (markedMemoryPathVisits d j (d.active v j k)) (c j (d.active v j k)) (hc j _) v
      ((markedMemoryPathVisits_mem d j _ v).mpr ⟨k,rfl⟩)
  exact hp.trans (hp2.trans (Sigma.ext rfl (heq_of_eq hl)))

theorem markedMemoryCappedPathIndependent_prime_injective
    (hP : ∀ i j,i≠j → Disjoint (P i) (P j)) :
    Function.Injective (markedMemoryIndependentPrime hZ
      (markedMemoryCappedPathIndependent (B := B) hZ d c hc hcap births)) := by
  let raw := markedMemoryCappedPathIndependent (B := B) hZ d c hc hcap births
  have hp (j : J) (a : MarkedMemoryPathUsedPrime d c j) :
      markedMemoryIndependentPrime hZ raw ⟨j,a⟩=a.1.1 :=
    congrArg (fun p : MarkedRawParticle (P j) => p.1.1)
      (markedMemoryCappedPathIndependent_particle (B := B) hZ d c hc hcap births j a)
  rintro ⟨i,a⟩ ⟨j,b⟩ heq
  have he : a.1.1=b.1.1 := (hp i a).symm.trans (heq.trans (hp j b))
  have hij : i=j := by
    by_contra hne
    exact (Finset.disjoint_left.mp (hP i j hne)) a.1.2 (he.symm ▸ b.1.2)
  subst j
  have hab : a=b := Subtype.ext (Subtype.ext he)
  cases hab
  rfl

theorem markedMemoryCappedPathIndependent_anchor
    (hP : ∀ i j,i≠j → Disjoint (P i) (P j)) (order : Fin n → J → Equiv.Perm (Fin pads)) :
    MarkedMemoryHistoryAnchorAdmissible hZ (markedMemoryIndependentHistory hZ
      (markedMemoryCappedPathIndependent (B := B) hZ d c hc hcap births) order) := by
  let raw := markedMemoryCappedPathIndependent (B := B) hZ d c hc hcap births
  have hinj := markedMemoryCappedPathIndependent_prime_injective (B := B) hZ d c hc hcap births hP
  apply markedMemoryIndependent_history_anchor_of_active_lines hZ raw hinj
  intro v j k
  have hp := markedMemoryCappedPathIndependent_active_particle (B := B) hZ d c hc hcap births v j k
  have hh : MarkedRawParticleHits (P j) (d.position v).1 (hZ _ (d.position v).2)
      (raw.particle j (raw.activeId v.val j k)) :=
    Eq.mpr (congrArg (MarkedRawParticleHits (P j) (d.position v).1 (hZ _ (d.position v).2)) hp)
      (markedRawAnchoredParticle_hits (P j) (d.active v j k) (d.position v).1 (hZ _ (d.position v).2))
  have hz := markedMemoryCappedPathIndependent_position (B := B) hZ d c hc hcap births v
  exact Eq.mpr (congrArg (fun z : Z => MarkedRawParticleHits (P j) z.1 (hZ _ z.2)
    (raw.particle j (raw.activeId v.val j k))) hz) hh

theorem markedMemoryCappedPathIndependent_birthDistinct
    (hP : ∀ i j,i≠j → Disjoint (P i) (P j)) (order : Fin n → J → Equiv.Perm (Fin pads)) :
    MarkedMemoryHistoryBirthDistinct hZ (markedMemoryIndependentHistory hZ
      (markedMemoryCappedPathIndependent (B := B) hZ d c hc hcap births) order) :=
  markedMemoryIndependent_birthDistinct_of_prime_injective hZ _ order
    (markedMemoryCappedPathIndependent_initial (B := B) hZ d c hc hcap births)
    (markedMemoryCappedPathIndependent_prime_injective (B := B) hZ d c hc hcap births hP)

end
end ArtinMatthews
