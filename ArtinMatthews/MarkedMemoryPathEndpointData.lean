module

public import ArtinMatthews.MarkedMemoryActivePathData
public import ArtinMatthews.MarkedMemoryEndpointData
public import ArtinMatthews.MarkedMemoryPrimeLifespanAnchor
public import ArtinMatthews.MarkedMinorArcRawGhostState
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
public import Std.Tactic.BVDecide.Normalize.Prop


set_option backward.privateInPublic true
@[expose] public section

/-! A compatible one-lifespan choice at each actual band prime gives
the bare finite endpoint data on exactly the used primes. No unused
particle labels or chronological history are stored. -/
namespace ArtinMatthews
noncomputable section
attribute [local instance] Classical.decEq Classical.propDecidable

variable {J : Type*} [Fintype J] {P : J → Finset Nat.Primes}
  {pads n : ℕ} {Z : Finset (ℤ × ℤ)}
  (hZ : ∀ z∈Z,IsCoprime z.1 z.2)
  (d : MarkedMemoryActivePathData P pads Z n)
  (c : MarkedMemoryPathPrimeChoices (P := P) (n := n))
  (hc : MarkedMemoryPathChoicesCompatible d hZ c)

def markedMemoryPathPrimeLines {j : J} (p : P j) : Fin (n+1) → MarkedRawPrimeLine p.1 :=
  fun v => markedPrimePositionLine (p.1:ℕ) (d.position v).1 (hZ _ (d.position v).2)

local notation "Used" => MarkedMemoryPathUsedPrime d c
local notation "visits" => markedMemoryPathVisits d
local notation "lines" => markedMemoryPathPrimeLines hZ d

def markedMemoryPathActiveUsed (v : Fin (n+1)) (j : J) : Fin (pads+1) ↪ Used j where
  toFun k := ⟨d.active v j k,Or.inl ⟨v,(markedMemoryPathVisits_mem d j _ v).mpr ⟨k,rfl⟩⟩⟩
  inj' := fun _ _ h => (d.active v j).injective (congrArg Subtype.val h)

def markedMemoryPathIncomingUsed (v : Fin n) (j : J) : Used j :=
  ⟨d.incoming v j,Or.inl ⟨v.succ,(markedMemoryPathVisits_mem d j _ v.succ).mpr (d.incoming_present v j)⟩⟩

def markedMemoryPathOutgoingUsed (v : Fin n) (j : J) : Used j :=
  ⟨d.outgoing v j,Or.inl ⟨v.castSucc,(markedMemoryPathVisits_mem d j _ v.castSucc).mpr (d.outgoing_present v j)⟩⟩

def markedMemoryPathEndpointData : MarkedMemoryEndpointData Used P pads Z n where
  first j a := ⟨markedMemoryPrimeFirst (visits j a.1) (c j a.1),by
    have h₁ := markedMemoryPrimeLifespan_nonempty (lines a.1) (visits j a.1) (c j a.1) (hc j a.1) a.2
    have h₂ := markedMemoryPrimeLast_bound (visits j a.1) (c j a.1)
    omega⟩
  last j a := ⟨markedMemoryPrimeLast (visits j a.1) (c j a.1),by
    have h := markedMemoryPrimeLast_bound (visits j a.1) (c j a.1)
    omega⟩
  active t j := Finset.univ.filter (fun a => (⟨t.val/2,by have h:=t.isLt; omega⟩ : Fin (n+1))∈visits j a.1)
  incoming := markedMemoryPathIncomingUsed d c
  outgoing := markedMemoryPathOutgoingUsed d c
  position := d.position
  activeId := markedMemoryPathActiveUsed d c
  particle j a := markedRawAnchoredParticle (P j) a.1
    (d.position (markedMemoryPrimeBirthVisit (visits j a.1) (c j a.1))).1
    (hZ _ (d.position (markedMemoryPrimeBirthVisit (visits j a.1) (c j a.1))).2)

omit [Fintype J] in
theorem markedMemoryPathEndpoint_first (j : J) (a : Used j) :
    ((markedMemoryPathEndpointData hZ d c hc).first j a).val=
      markedMemoryPrimeFirst (visits j a.1) (c j a.1) := rfl

omit [Fintype J] in
theorem markedMemoryPathEndpoint_last (j : J) (a : Used j) :
    ((markedMemoryPathEndpointData hZ d c hc).last j a).val=
      markedMemoryPrimeLast (visits j a.1) (c j a.1) := rfl

omit [Fintype J] in
theorem markedMemoryPathEndpoint_active (t : Fin (2*n+2)) (j : J) (a : Used j) :
    a∈(markedMemoryPathEndpointData hZ d c hc).active t j ↔
      ∃ k,d.active ⟨t.val/2,by have h:=t.isLt; omega⟩ j k=a.1 := by
  simp only [markedMemoryPathEndpointData,Finset.mem_filter,Finset.mem_univ,true_and,
    markedMemoryPathVisits_mem]

omit [Fintype J] in
theorem markedMemoryPathEndpoint_position (v : Fin (n+1)) :
    (markedMemoryPathEndpointData hZ d c hc).position v=d.position v := rfl

omit [Fintype J] in
theorem markedMemoryPathEndpoint_particle (j : J) (a : Used j) :
    (markedMemoryPathEndpointData hZ d c hc).particle j a=
      markedRawAnchoredParticle (P j) a.1
        (d.position (markedMemoryPrimeBirthVisit (visits j a.1) (c j a.1))).1
        (hZ _ (d.position (markedMemoryPrimeBirthVisit (visits j a.1) (c j a.1))).2) := rfl

end
end ArtinMatthews
