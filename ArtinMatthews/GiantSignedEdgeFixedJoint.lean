module

public import ArtinMatthews.GiantSignedEdgeJointData
public import ArtinMatthews.GiantSignedEdgeInjectionJoint
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

/-! The selected target primes are supplied by old memory. The exact
factorial identity leaves only the survivor factorial in the joint measure. -/
namespace ArtinMatthews
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

abbrev GiantSignedPrimeTuple {J : Type*} (P : J → Finset ℕ) (n : J → ℕ) :=
  (j : J) → Fin (n j) → P j

abbrev GiantSignedParticleTuple {J : Type*} (P : J → Finset ℕ) (n : J → ℕ) :=
  (j : J) → Fin (n j) → GiantSignedParticle (P j)

def giantSignedDegreeMass {J : Type*} [Fintype J] {P : J → Finset ℕ}
    (ν : (j : J) → P j → ℂ) {n : J → ℕ} (u : GiantSignedParticleTuple P n) : ℂ :=
  (∏ j, ∏ i, ν j (u j i).1) / (∏ j, (Nat.factorial (n j) : ℂ))

theorem giantSignedDegreeMass_actual {J : Type*} [Fintype J] {P : J → Finset ℕ}
    (ν : (j : J) → P j → ℝ) {n : J → ℕ} (u : GiantSignedParticleTuple P n) :
    giantSignedDegreeMass (fun j p => (ν j p : ℂ)) u =
      (giantSignedMemoryMass ν ⟨n, u⟩ : ℂ) := by
  simp only [giantSignedDegreeMass, giantSignedMemoryMass, Complex.ofReal_prod,
    Complex.ofReal_div, Complex.ofReal_natCast, Finset.prod_div_distrib]

def GiantSignedTupleHits {J : Type*} {P : J → Finset ℕ} {a : J → ℕ}
    (d : ℤ) (p : GiantSignedParticleTuple P a) (q : GiantSignedPrimeTuple P a) : Prop :=
  ∀ j i, giantSignedParticleTranslate d (p j i) = giantSignedParticleAt 0 (q j i)

theorem giantSignedTupleHits_iff {J : Type*} {P : J → Finset ℕ} {a : J → ℕ}
    (d : ℤ) (p : GiantSignedParticleTuple P a) (q : GiantSignedPrimeTuple P a) :
    GiantSignedTupleHits d p q ↔ p = fun j i => giantSignedParticleAt (-d) (q j i) := by
  simp only [GiantSignedTupleHits, giantSignedParticleTranslate_zero_iff]
  exact ⟨fun h => funext fun j => funext fun i => h j i, fun h j i => congrFun (congrFun h j) i⟩

section Fixed
variable {J : Type*} [Fintype J] [DecidableEq J] {P : J → Finset ℕ}
variable [∀ j, ∀ p : P j, NeZero p.val]
variable {n a b : J → ℕ}

/-- Actual ordered promotion, with an arbitrary coupled endpoint test. -/
theorem giantSignedEdge_fixed_joint
    (ν : (j : J) → P j → ℂ) (d : ℤ)
    (q : GiantSignedPrimeTuple P a) (s : GiantSignedPrimeTuple P b)
    (F : GiantSignedMemory P → GiantSignedMemory P → ℂ)
    (hF : ∀ out, GiantSignedMemorySymmetric (fun old => F old out)) :
    (∑ old : GiantSignedParticleTuple P (fun j => n j + a j),
      giantSignedDegreeMass ν old *
        ∑ e : (j : J) → Fin (a j) ↪ Fin (n j + a j),
          if GiantSignedTupleHits d (fun j => old j ∘ e j) q then
            F ⟨fun j => n j + a j, old⟩
              (giantSignedEdgeOutput d (fun j => giantSignedRetrievalSurvivors (e j) (old j)) s)
          else 0) =
      (∏ j, ∏ i, ν j (q j i)) *
        ∑ u : GiantSignedParticleTuple P n,
          giantSignedDegreeMass ν u * F (giantSignedEdgeInput d u q) (giantSignedEdgeOutput d u s) := by
  classical
  let z : GiantSignedParticleTuple P a := fun j i => giantSignedParticleAt (-d) (q j i)
  let H := fun (old : GiantSignedParticleTuple P (fun j => n j + a j))
      (p : GiantSignedParticleTuple P a) (u : GiantSignedParticleTuple P n) =>
    if p = z then F ⟨fun j => n j + a j, old⟩ (giantSignedEdgeOutput d u s) else 0
  have hH : ∀ p u, MarkedRawGroupedTupleSymmetric (fun j => n j + a j)
      (fun old => H old p u) := by
    intro p u old σ
    dsimp only [H]
    by_cases hp : p = z
    · simp only [hp, ite_true]
      exact hF (giantSignedEdgeOutput d u s) ⟨fun j => n j + a j, old⟩ σ
    · simp only [hp, ite_false]
  have he := giantSignedMemory_injection_joint_factorial
    (fun j (p : GiantSignedParticle (P j)) => ν j p.1) H hH
  simp only [H, z, ← giantSignedTupleHits_iff] at he
  unfold giantSignedDegreeMass
  rw [he]
  rw [Finset.sum_comm, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro u _
  simp only [giantSignedTupleHits_iff, mul_ite, mul_zero]
  rw [Finset.sum_ite_eq']
  simp only [Finset.mem_univ, ite_true, giantSignedParticleAt]
  simp only [giantSignedEdgeInput, giantSignedParticleAt]
  ring

end Fixed

section Damped
variable {J : Type*} [Fintype J] {P : J → Finset ℕ}

/-- Both actual pending half-dampings remain in the coupled test. -/
def giantSignedEdgeDampedTest (ρ : ℝ)
    (F : GiantSignedMemory P → GiantSignedMemory P → ℂ)
    (old out : GiantSignedMemory P) : ℂ :=
  (giantSignedPendingDamping ρ old : ℂ) * (giantSignedPendingDamping ρ out : ℂ) * F old out

theorem giantSignedEdgeDampedTest_symmetric (ρ : ℝ)
    (F : GiantSignedMemory P → GiantSignedMemory P → ℂ)
    (hF : ∀ out, GiantSignedMemorySymmetric (fun old => F old out))
    (out : GiantSignedMemory P) :
    GiantSignedMemorySymmetric (fun old => giantSignedEdgeDampedTest ρ F old out) := by
  intro old σ
  dsimp only [giantSignedEdgeDampedTest]
  rw [giantSignedPendingDamping_permute]
  exact congrArg (fun z : ℂ =>
    (giantSignedPendingDamping ρ old : ℂ) * (giantSignedPendingDamping ρ out : ℂ) * z)
    (hF out old σ)

end Damped
end
end ArtinMatthews
