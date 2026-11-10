module

public import ArtinMatthews.MarkedMinorArcRawGhostMemoryNormalForm
public import ArtinMatthews.MarkedMinorArcRawGhostGroupedDegreeAdjoint
public import ArtinMatthews.MarkedMinorArcRawMemoryDegreeFamily
public import Mathlib.CategoryTheory.Category.Basic
public import ArtinMatthews.MarkedMinorArcRawGhostDegreeTarget
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
public import Mathlib.RingTheory.WittVector.IsPoly
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
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! Exact degree normal form of the literal total-truncated signed rule.
No symmetry of the source or target tests is needed for this reindexing. -/
namespace ArtinMatthews
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

def markedRawGhostDegreeSourceFactor {J : Type*} [Fintype J]
    (P : J → Finset Nat.Primes) (ν : (j : J) → ↥(P j) → ℝ) {B : ℕ}
    (g : MarkedRawMemory P B → ℂ) (t : MarkedRawGhostDegrees J B)
    (old : (j : J) → Fin (t.survivors j+t.deleted j) → MarkedRawParticle (P j)) : ℂ :=
  ((∏ j,∏ i,(ν j (old j i).1:ℂ))/(∏ j,(Nat.factorial (t.survivors j+t.deleted j):ℂ)))*
    g (markedRawMemoryOfDegrees P (fun j => t.survivors j+t.deleted j) t.source_le old)

def markedRawGhostDegreeCharges {J : Type*} [Fintype J] {B : ℕ}
    (δ γ : J → ℝ) (t : MarkedRawGhostDegrees J B) : ℂ :=
  ∏ j,(δ j:ℂ)^(t.deleted j)*(γ j:ℂ)^(t.born j)

def markedRawGhostDegreeSurvival {J : Type*} [Fintype J]
    (P : J → Finset Nat.Primes) (s : J → ℝ) {B : ℕ} (z : ℤ × ℤ) (hz : IsCoprime z.1 z.2)
    (a : MarkedRawGhostDegreeShape J B)
    (old : (j : J) → Fin (a.1.survivors j+a.1.deleted j) → MarkedRawParticle (P j)) : ℂ :=
  ∏ j,(s j:ℂ)^(markedRawTupleHitCount (P j) z hz
    (markedRawSurvivorTupleCast (a.2 j).1 (markedRawDeletionBatch_survivor_card rfl (a.2 j)) (old j)))

def markedRawGhostDegreeBirthTerm {J : Type*} [Fintype J]
    (P : J → Finset Nat.Primes) (ν : (j : J) → ↥(P j) → ℝ) {B : ℕ}
    (z : ℤ × ℤ) (hz : IsCoprime z.1 z.2) (f : MarkedRawMemory P B → ℂ)
    (a : MarkedRawGhostDegreeShape J B)
    (old : (j : J) → Fin (a.1.survivors j+a.1.deleted j) → MarkedRawParticle (P j))
    (births : (j : J) → Fin (a.1.born j) → ↥(P j)) : ℂ :=
  ((∏ j,∏ i,(ν j (births j i):ℂ))/(∏ j,(Nat.factorial (a.1.born j):ℂ)))*
    f (markedRawMemoryOfDegrees P (fun j => a.1.survivors j+a.1.born j) a.1.target_le
      (fun j => Fin.addCases
        (markedRawSurvivorTupleCast (a.2 j).1 (markedRawDeletionBatch_survivor_card rfl (a.2 j)) (old j))
        (markedRawAnchoredBatch (P j) z hz (a.1.born j) (births j))))

set_option backward.isDefEq.respectTransparency false in
theorem markedRawGhost_degree_pairing_term {J : Type*} [Fintype J] [DecidableEq J]
    (P : J → Finset Nat.Primes) (ν : (j : J) → ↥(P j) → ℝ) (δ γ s : J → ℝ)
    {B : ℕ} (z : ℤ × ℤ) (hz : IsCoprime z.1 z.2) (f g : MarkedRawMemory P B → ℂ)
    (a : MarkedRawGhostDegreeShape J B) (data : MarkedRawGhostDegreePayload P z hz a) :
    markedRawGhostMemoryChoicePairing ν δ γ s z hz f g
      (markedRawGhostDegreeMemoryChoice P z hz a data)=
      markedRawGhostDegreeSourceFactor P ν g a.1 data.1.1 * markedRawGhostDegreeCharges δ γ a.1 *
        markedRawGhostDegreeSurvival P s z hz a data.1.1 *
        markedRawGhostDegreeBirthTerm P ν z hz f a data.1.1 data.1.2 := by
  unfold markedRawGhostMemoryChoicePairing
  erw [markedRawGhost_degree_charge_coefficient,markedRawGhost_degree_birth_mass,
    markedRawGhost_degree_target,markedRawGhost_degree_source,markedRawMemoryOfDegrees_mass_complex]
  simp only [Complex.ofReal_mul,Complex.ofReal_prod,Complex.ofReal_pow,Complex.ofReal_div,
    Complex.ofReal_natCast]
  rw [Finset.prod_div_distrib]
  let A := (∏ j,∏ i,(ν j (data.1.1 j i).1:ℂ))/(∏ j,(Nat.factorial (a.1.survivors j+a.1.deleted j):ℂ))
  let G := g (markedRawMemoryOfDegrees P (fun j => a.1.survivors j+a.1.deleted j) a.1.source_le data.1.1)
  let D := ∏ j,(δ j:ℂ)^(a.1.deleted j)
  let H := markedRawGhostDegreeSurvival P s z hz a data.1.1
  let C := ∏ j,(γ j:ℂ)^(a.1.born j)
  let E := markedRawGhostDegreeBirthTerm P ν z hz f a data.1.1 data.1.2
  let U := (∏ j,∏ i,(ν j (data.1.2 j i):ℂ))/(∏ j,(Nat.factorial (a.1.born j):ℂ))
  let F := f (markedRawMemoryOfDegrees P (fun j => a.1.survivors j+a.1.born j) a.1.target_le
    (markedRawGhostDegreeTargetTuple P z hz a data))
  have hE : U*F=E := rfl
  unfold markedRawGhostDegreeSourceFactor markedRawGhostDegreeCharges
  simp only [Finset.prod_mul_distrib]
  change A*G*((D*H*C)*U)*F=A*G*(D*C)*H*E
  rw [← hE]
  ring

set_option backward.isDefEq.respectTransparency false in
theorem markedRawGhost_degree_payload_pairing {J : Type*} [Fintype J] [decJ : DecidableEq J]
    (P : J → Finset Nat.Primes) (ν : (j : J) → ↥(P j) → ℝ) (δ γ s : J → ℝ)
    {B : ℕ} (z : ℤ × ℤ) (hz : IsCoprime z.1 z.2) (f g : MarkedRawMemory P B → ℂ)
    (a : MarkedRawGhostDegreeShape J B) :
    (∑ data : MarkedRawGhostDegreePayload P z hz a,
      markedRawGhostMemoryChoicePairing ν δ γ s z hz f g (markedRawGhostDegreeMemoryChoice P z hz a data))=
      ∑ old : (j : J) → Fin (a.1.survivors j+a.1.deleted j) → MarkedRawParticle (P j),
        markedRawGhostDegreeSourceFactor P ν g a.1 old * markedRawGhostDegreeCharges δ γ a.1 *
          (if MarkedRawGhostDegreeAllowed P z hz a old then 1 else 0) *
          markedRawGhostDegreeSurvival P s z hz a old *
          ∑ births : (j : J) → Fin (a.1.born j) → ↥(P j),
            markedRawGhostDegreeBirthTerm P ν z hz f a old births := by
  classical
  cases Subsingleton.elim decJ (Classical.decEq J)
  refine (markedRawGhost_degree_payload_sum P z hz a
    (fun data => markedRawGhostMemoryChoicePairing ν δ γ s z hz f g
      (markedRawGhostDegreeMemoryChoice P z hz a data))).trans ?_
  apply Finset.sum_congr rfl
  intro old _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro births _
  split_ifs with h
  · erw [markedRawGhost_degree_pairing_term]
    simp only [mul_one]
  · simp only [mul_zero,zero_mul]

set_option backward.isDefEq.respectTransparency false in
theorem markedRawGhostMemoryRule_degree_normalForm {J : Type*} [Fintype J] [decJ : DecidableEq J]
    (P : J → Finset Nat.Primes) (ν : (j : J) → ↥(P j) → ℝ) (δ γ s : J → ℝ)
    {B : ℕ} (z : ℤ × ℤ) (hz : IsCoprime z.1 z.2) (f g : MarkedRawMemory P B → ℂ) :
    (∑ m : MarkedRawMemory P B,(markedRawMemoryMass ν m:ℂ)*g m*
      markedRawGhostMemoryRule ν δ γ s z hz f m)=
      ∑ t : MarkedRawGhostDegrees J B,
        ∑ old : (j : J) → Fin (t.survivors j+t.deleted j) → MarkedRawParticle (P j),
          markedRawGhostDegreeSourceFactor P ν g t old *
            markedRawGhostGroupedDegreeComponent P (fun j p => (ν j p:ℂ)) z hz
              t.survivors t.deleted t.born (fun j => (δ j:ℂ)) (fun j => (γ j:ℂ)) (fun j => (s j:ℂ))
              (fun b => f (markedRawMemoryOfDegrees P (fun j => t.survivors j+t.born j) t.target_le b)) old := by
  classical
  cases Subsingleton.elim decJ (Classical.decEq J)
  refine (markedRawGhostMemoryRule_pairing_choices ν δ γ s z hz f g).trans ?_
  refine (markedRawGhost_memory_degree_sum P z hz
    (markedRawGhostMemoryChoicePairing ν δ γ s z hz f g)).trans ?_
  simp only [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro t _
  simp_rw [markedRawGhost_degree_payload_pairing]
  let F (S : (j : J) → MarkedRawDeletionBatch (t.survivors j+t.deleted j) (t.deleted j))
      (old : (j : J) → Fin (t.survivors j+t.deleted j) → MarkedRawParticle (P j)) : ℂ :=
    markedRawGhostDegreeSourceFactor P ν g t old * markedRawGhostDegreeCharges δ γ t *
      (if MarkedRawGhostDegreeAllowed P z hz ⟨t,S⟩ old then 1 else 0) *
      markedRawGhostDegreeSurvival P s z hz ⟨t,S⟩ old *
      ∑ births : (j : J) → Fin (t.born j) → ↥(P j),
        markedRawGhostDegreeBirthTerm P ν z hz f ⟨t,S⟩ old births
  change (∑ S,∑ old,F S old)=_
  calc
    _ = ∑ old,∑ S,F S old := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro old _
      dsimp only [F]
      simp_rw [← markedRawGhostDegreeAllowed_indicator]
      unfold markedRawGhostGroupedDegreeComponent markedRawGhostDegreeCharges markedRawGhostDegreeSurvival
        markedRawGhostDegreeBirthTerm
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro S _
      apply Finset.sum_congr rfl
      intro births _
      ring

end
end ArtinMatthews
