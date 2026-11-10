module

/- Adapted in the Artin–Matthews source bundle. The source, upstream and packaged digests are recorded in SOURCE_MANIFEST.json. -/

public import OAI.RepresentationTheory.Weil.Local.OscillatorProjection
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


set_option backward.privateInPublic true
@[expose] public section

/-! # Oscillator Rescaling -/

namespace OAI.RepresentationTheory.Weil.Local.OscillatorRescaling.Construction

noncomputable section

/-! Character rescaling transports the actual oscillator and bare groups. -/

open _root_.Matrix _root_.MeasureTheory

theorem heisenbergFunction_character_rescaling {k : Type} [Field k] {n : ℕ}
    (ψ η : AddChar k ℂ) (c : k) (hη : ∀ t, η t = ψ (c * t))
    (v : FunctionsMetaplectic.Construction.PhaseSpace k n) (f : FunctionsMetaplectic.Construction.Position k n → ℂ) :
    FunctionsMetaplectic.Construction.heisenbergFunction η v f = FunctionsMetaplectic.Construction.heisenbergFunction ψ (Generators.Construction.phaseScaleMatrix n c *ᵥ v) f := by
  funext x
  simp only [FunctionsMetaplectic.Construction.heisenbergFunction, Generators.Construction.phaseScaleMatrix_apply_inl, Generators.Construction.phaseScaleMatrix_apply_inr, hη]
  congr 2
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem heisenbergGraph_character_rescaling {k : Type} [NormedField k] {n : ℕ}
    (ψ η : AddChar k ℂ) (c : k) (hη : ∀ t, η t = ψ (c * t))
    (v : FunctionsMetaplectic.Construction.PhaseSpace k n) (f h : FunctionsMetaplectic.Construction.schwartzBruhat k n) :
    FunctionsMetaplectic.Construction.heisenbergGraph η v f h ↔ FunctionsMetaplectic.Construction.heisenbergGraph ψ (Generators.Construction.phaseScaleMatrix n c *ᵥ v) f h := by
  unfold FunctionsMetaplectic.Construction.heisenbergGraph
  rw [heisenbergFunction_character_rescaling ψ η c hη]

def characterRescaleOscillator {k : Type} [NormedField k] [LocallyCompactSpace k]
    [MeasurableSpace k] [BorelSpace k] (n : ℕ)
    (ψ η : AddChar k ℂ) (c : k) (hc : c ≠ 0) (hη : ∀ t, η t = ψ (c * t)) :
    FunctionsMetaplectic.Construction.Oscillator k n η →* FunctionsMetaplectic.Construction.Oscillator k n ψ where
  toFun a := ⟨(Generators.Construction.phaseRescaleSymplectic n c hc a.val.1, a.val.2), a.property.1, by
    intro v f h
    obtain ⟨u, rfl⟩ := Generators.Construction.phaseScaleMatrix_surjective n c hc v
    rw [Generators.Construction.phaseRescaleSymplectic_action]
    rw [← heisenbergGraph_character_rescaling ψ η c hη,
      ← heisenbergGraph_character_rescaling ψ η c hη]
    exact a.property.2 u f h⟩
  map_one' := by
    apply Subtype.ext
    change (Generators.Construction.phaseRescaleSymplectic n c hc 1, 1) = (1, 1)
    rw [map_one]
  map_mul' a b := by
    apply Subtype.ext
    change (Generators.Construction.phaseRescaleSymplectic n c hc (a.val.1 * b.val.1), a.val.2 * b.val.2) =
      (Generators.Construction.phaseRescaleSymplectic n c hc a.val.1 * Generators.Construction.phaseRescaleSymplectic n c hc b.val.1,
        a.val.2 * b.val.2)
    rw [map_mul]

theorem characterRescaleOscillator_projection {k : Type} [NormedField k] [LocallyCompactSpace k]
    [MeasurableSpace k] [BorelSpace k] {n : ℕ}
    (ψ η : AddChar k ℂ) (c : k) (hc : c ≠ 0) (hη : ∀ t, η t = ψ (c * t))
    (a : FunctionsMetaplectic.Construction.Oscillator k n η) :
    OscillatorProjection.Construction.oscillatorProjection k n ψ (characterRescaleOscillator n ψ η c hc hη a) =
      Generators.Construction.phaseRescaleSymplectic n c hc (OscillatorProjection.Construction.oscillatorProjection k n η a) := rfl

theorem characterRescaleOscillator_minus {k : Type} [NormedField k] [LocallyCompactSpace k]
    [MeasurableSpace k] [BorelSpace k] (n : ℕ)
    (ψ η : AddChar k ℂ) (c : k) (hc : c ≠ 0) (hη : ∀ t, η t = ψ (c * t)) :
    characterRescaleOscillator n ψ η c hc hη (FunctionsMetaplectic.Construction.oscillatorMinus k n η) = FunctionsMetaplectic.Construction.oscillatorMinus k n ψ := by
  apply Subtype.ext
  change (Generators.Construction.phaseRescaleSymplectic n c hc 1, LinearEquiv.neg ℂ) = (1, LinearEquiv.neg ℂ)
  rw [map_one]

theorem characterRescaleOscillator_mem {k : Type} [NormedField k] [LocallyCompactSpace k]
    [MeasurableSpace k] [BorelSpace k] {n : ℕ}
    (ψ η : AddChar k ℂ) (c : k) (hc : c ≠ 0) (hη : ∀ t, η t = ψ (c * t))
    (a : FunctionsMetaplectic.Construction.Metaplectic k n η) :
    characterRescaleOscillator n ψ η c hc hη a.val ∈ FunctionsMetaplectic.Construction.metaplecticSubgroup k n ψ := by
  let F := characterRescaleOscillator n ψ η c hc hη
  have hle : FunctionsMetaplectic.Construction.metaplecticSubgroup k n η ≤ (FunctionsMetaplectic.Construction.metaplecticSubgroup k n ψ).comap F := by
    change Subgroup.closure (commutatorSet (FunctionsMetaplectic.Construction.Oscillator k n η) ∪ {FunctionsMetaplectic.Construction.oscillatorMinus k n η}) ≤ _
    rw [Subgroup.closure_le]
    intro x hx
    change F x ∈ FunctionsMetaplectic.Construction.metaplecticSubgroup k n ψ
    rcases hx with hx | hx
    · obtain ⟨a, b, rfl⟩ := mem_commutatorSet_iff.mp hx
      rw [map_commutatorElement]
      exact Subgroup.subset_closure (Or.inl (commutator_mem_commutatorSet _ _))
    · obtain rfl := Set.mem_singleton_iff.mp hx
      rw [characterRescaleOscillator_minus]
      exact Subgroup.subset_closure (Or.inr rfl)
  exact hle a.property

def characterRescaleMetaplectic {k : Type} [NormedField k] [LocallyCompactSpace k]
    [MeasurableSpace k] [BorelSpace k] {n : ℕ}
    (ψ η : AddChar k ℂ) (c : k) (hc : c ≠ 0) (hη : ∀ t, η t = ψ (c * t))
    (a : FunctionsMetaplectic.Construction.Metaplectic k n η) : FunctionsMetaplectic.Construction.Metaplectic k n ψ :=
  ⟨characterRescaleOscillator n ψ η c hc hη a.val,
    characterRescaleOscillator_mem ψ η c hc hη a⟩

end

end OAI.RepresentationTheory.Weil.Local.OscillatorRescaling.Construction
