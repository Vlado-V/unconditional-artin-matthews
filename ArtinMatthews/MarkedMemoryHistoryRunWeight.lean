module

public import ArtinMatthews.MarkedMemoryHistoryPromotionTrace
public import ArtinMatthews.MarkedRawBoundary
public import ArtinMatthews.MarkedMemoryHistoryWeightTelescope
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
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! Exact grouping of actual nu and V events by their computed lifespan
identities. The factors below are obtained from literal performed births
and old-only promotions. No independent lifespan expansion is assumed. -/
namespace ArtinMatthews
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

variable {J : Type*} [Fintype J] [DecidableEq J]
  {P : J → Finset Nat.Primes} {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
  (ν : (j : J) → ↥(P j) → ℝ) (V : J → ℝ)
  (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2)

def markedMemoryHistoryFiniteTraceEquiv {n : ℕ} {s : MarkedRawState P (pads+1) B Z}
    (history : MarkedMemoryChronologicalHistory hZ n s) :
    MarkedMemoryHistoryTraceAddress hZ history ≃
      (MarkedMemoryPopulationIndex s ⊕ MarkedMemoryHistoryBirths hZ history) :=
  Equiv.sumCongr (Equiv.refl _) (markedMemoryHistoryTraceBirthEquiv hZ history)

instance markedMemoryHistoryTraceAddress_fintype {n : ℕ} {s : MarkedRawState P (pads+1) B Z}
    (history : MarkedMemoryChronologicalHistory hZ n s) :
    Fintype (MarkedMemoryHistoryTraceAddress hZ history) :=
  Fintype.ofEquiv _ (markedMemoryHistoryFiniteTraceEquiv hZ history).symm

def markedMemoryHistoryTraceBirthMass {n : ℕ} {s : MarkedRawState P (pads+1) B Z}
    (history : MarkedMemoryChronologicalHistory hZ n s) : MarkedMemoryHistoryTraceAddress hZ history → ℝ :=
  Sum.elim (fun _ => 1) (fun b =>
    let finite := markedMemoryHistoryTraceBirthEquiv hZ history b
    let p := markedMemoryHistoryBirthLabel hZ history finite
    (if markedMemoryHistoryBirthIsGhost hZ history finite then V p.1 else 1) * ν p.1 p.2)

/-- Number of actual old-only promotions belonging to this particular
computed lifespan. Fresh draws and stores are never included. -/
def markedMemoryHistoryRunCount {n : ℕ} {s : MarkedRawState P (pads+1) B Z}
    (history : MarkedMemoryChronologicalHistory hZ n s) (a : MarkedMemoryHistoryTraceAddress hZ history) : ℕ :=
  Fintype.card {r : MarkedMemoryHistoryPromotionIndex hZ history //
    markedMemoryHistoryPromotionOrigin hZ history r = a}

def markedMemoryHistoryRunMass {n : ℕ} {s : MarkedRawState P (pads+1) B Z}
    (history : MarkedMemoryChronologicalHistory hZ n s) (a : MarkedMemoryHistoryTraceAddress hZ history) : ℝ :=
  ∏ r : {r : MarkedMemoryHistoryPromotionIndex hZ history //
    markedMemoryHistoryPromotionOrigin hZ history r = a},
      (V (markedMemoryHistoryPromotionGroup hZ history r.1))⁻¹

omit [DecidableEq J] in
theorem markedMemoryHistoryBirthMass_trace {n : ℕ} {s : MarkedRawState P (pads+1) B Z}
    (history : MarkedMemoryChronologicalHistory hZ n s) :
    markedMemoryHistoryBirthMass ν V hZ history =
      ∏ a : MarkedMemoryHistoryTraceAddress hZ history, markedMemoryHistoryTraceBirthMass ν V hZ history a := by
  let f (b : MarkedMemoryHistoryBirths hZ history) : ℝ :=
    let p := markedMemoryHistoryBirthLabel hZ history b
    (if markedMemoryHistoryBirthIsGhost hZ history b then V p.1 else 1) * ν p.1 p.2
  have heq (x : MarkedMemoryPopulationIndex s ⊕ MarkedMemoryHistoryBirths hZ history) :
      markedMemoryHistoryTraceBirthMass ν V hZ history
          ((markedMemoryHistoryFiniteTraceEquiv hZ history).symm x) =
        Sum.elim (fun _ => 1) f x := by
    cases x with
    | inl x => rfl
    | inr b =>
      change f ((markedMemoryHistoryTraceBirthEquiv hZ history)
        ((markedMemoryHistoryTraceBirthEquiv hZ history).symm b)) = f b
      rw [Equiv.apply_symm_apply]
  symm
  rw [← Equiv.prod_comp (markedMemoryHistoryFiniteTraceEquiv hZ history).symm]
  simp_rw [heq]
  rw [Fintype.prod_sum_type]
  simp only [Sum.elim_inl, Sum.elim_inr, Finset.prod_const_one, one_mul]
  rfl

/-- Regrouping uses the actual origin map of each charged promotion. -/
theorem markedMemoryHistoryPromotionMass_trace {n : ℕ} {s : MarkedRawState P (pads+1) B Z}
    (history : MarkedMemoryChronologicalHistory hZ n s) :
    markedMemoryHistoryPromotionMass V hZ history =
      ∏ a : MarkedMemoryHistoryTraceAddress hZ history, markedMemoryHistoryRunMass V hZ history a := by
  classical
  exact (Fintype.prod_fiberwise (markedMemoryHistoryPromotionOrigin hZ history)
    (fun r => (V (markedMemoryHistoryPromotionGroup hZ history r))⁻¹)).symm

/-- Birth and retrieval masses grouped by the actual finite family of
computed lifespans, including any initial identities with no birth charge. -/
theorem markedMemoryHistoryPrimeMass_lifespans {n : ℕ} {s : MarkedRawState P (pads+1) B Z}
    (history : MarkedMemoryChronologicalHistory hZ n s) :
    markedMemoryHistoryPrimeMass ν V hZ history =
      ∏ a : MarkedMemoryHistoryTraceAddress hZ history,
        markedMemoryHistoryTraceBirthMass ν V hZ history a * markedMemoryHistoryRunMass V hZ history a := by
  unfold markedMemoryHistoryPrimeMass
  rw [markedMemoryHistoryBirthMass_trace, markedMemoryHistoryPromotionMass_trace, Finset.prod_mul_distrib]

/-- The original signed history coefficient now has one genuine nu/V
factor per computed lifespan; all signs, hit damping, factorials, slot
probabilities, physical tests and Fourier factors remain in the residual. -/
theorem markedMemoryChronologicalWeight_lifespan_factor
    (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ) (d₀ Y Q : ℝ)
    (qStage : ℕ → ℝ) (χ : ℕ → MarkedRawState P (pads+1) B Z → ℂ)
    (n j : ℕ) {s : MarkedRawState P (pads+1) B Z}
    (history : MarkedMemoryChronologicalHistory hZ n s) :
    markedMemoryChronologicalWeight ν V hZ ψ η d₀ Y Q 1 qStage χ n j history =
      ((∏ a : MarkedMemoryHistoryTraceAddress hZ history,
        markedMemoryHistoryTraceBirthMass ν V hZ history a * markedMemoryHistoryRunMass V hZ history a : ℝ) : ℂ) *
          markedMemoryHistoryResidual hZ ψ η d₀ Y Q qStage χ n j history := by
  rw [markedMemoryChronologicalWeight_prime_factor, markedMemoryHistoryPrimeMass_lifespans]

/-- Empty boundary memory removes the auxiliary rho factors before the
same actual lifespan grouping. -/
theorem markedMemoryChronologicalWeight_lifespan_factor_empty
    (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ) (d₀ Y Q ρ : ℝ) (hρ : ρ ≠ 0)
    (qStage : ℕ → ℝ) (χ : ℕ → MarkedRawState P (pads+1) B Z → ℂ)
    (n j : ℕ) {s : MarkedRawState P (pads+1) B Z}
    (history : MarkedMemoryChronologicalHistory hZ n s)
    (hs : s.2.2 = markedRawBoundaryEmptyMemory P B)
    (ht : (markedMemoryChronologicalTarget hZ history).2.2 = markedRawBoundaryEmptyMemory P B) :
    markedMemoryChronologicalWeight ν V hZ ψ η d₀ Y Q ρ qStage χ n j history =
      ((∏ a : MarkedMemoryHistoryTraceAddress hZ history,
        markedMemoryHistoryTraceBirthMass ν V hZ history a * markedMemoryHistoryRunMass V hZ history a : ℝ) : ℂ) *
          markedMemoryHistoryResidual hZ ψ η d₀ Y Q qStage χ n j history := by
  rw [markedMemoryChronologicalWeight_rho_empty ν V hZ ψ η d₀ Y Q ρ hρ qStage χ n j history hs ht,
    markedMemoryChronologicalWeight_lifespan_factor]

end
end ArtinMatthews
