module

public import ArtinMatthews.MarkedMemoryIndependentWeight
public import ArtinMatthews.MarkedMemoryNormalizedHistoryIndex


set_option backward.privateInPublic true
@[expose] public section

/-! Elementwise source weights on normalized finite endpoint data. The
direct scalar uses the real first/last and active incidences; the exact
birth factorial and full signed edge residual remain separate factors. -/
namespace ArtinMatthews
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.decEq Classical.propDecidable

variable {J : Type*} [Fintype J] {A : J → Type*}
  [∀ j,Fintype (A j)] [∀ j,DecidableEq (A j)]
  {P : J → Finset Nat.Primes} {pads B n : ℕ} {Z : Finset (ℤ × ℤ)}
  (hZ : ∀ z ∈ Z,IsCoprime z.1 z.2)

def markedMemoryIndependentEndpointScalar
    (d : MarkedMemoryIndependentLifespans (A := A) (P := P) (pads := pads) (B := B) hZ n)
    (q : ℝ) (a : Σ j,A j) : ℝ :=
  ∏ v : Fin (n+1),
    (if (d.lifespan a.1).first a.2≤2*v.val ∧ 2*v.val≤(d.lifespan a.1).last a.2 ∧
        ¬(d.lifespan a.1).active (2*v.val) a.2 then
      (if (d.lifespan a.1).last a.2=2*v.val then
        -markedMemoryEta q n v*markedMemoryIndependentLineHit hZ d a v
       else 1-markedMemoryEta q n v*markedMemoryIndependentLineHit hZ d a v)
     else 1) *
    (if (d.lifespan a.1).first a.2=2*v.val+1 ∧ 2*v.val+1≤(d.lifespan a.1).last a.2 ∧
        ¬(d.lifespan a.1).active (2*v.val) a.2 then
      -markedMemoryEta q n v*markedMemoryIndependentLineHit hZ d a v else 1)

theorem markedMemoryIndependentEndpointScalar_eq
    (d : MarkedMemoryIndependentLifespans (A := A) (P := P) (pads := pads) (B := B) hZ n)
    (q : ℝ) (a : Σ j,A j) :
    markedMemoryIndependentEndpointScalar hZ d q a=markedMemoryIndependentLifespanSourceScalar hZ d q a :=
  (markedMemoryIndependentLifespanSourceScalar_endpoints hZ d q a).symm

variable (s : MarkedRawState P (pads+1) B Z)
  (ν : (j : J) → ↥(P j) → ℝ) (V : J → ℝ) (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ)
  (d₀ Y Q : ℝ) (q : ℝ) (χ : ℕ → MarkedRawState P (pads+1) B Z → ℂ)

def markedMemoryNormalizedEndpointWeight
    (i : MarkedMemoryNormalizedHistoryIndex (A := A) (n := n) hZ s) : ℂ :=
  let d := markedMemoryFiniteTableau_toIndependent hZ i.1.1.1
  let H := markedMemoryIndependentHistory hZ d i.1.2
  (((∏ a : Σ j,A j,markedMemoryIndependentBirthMass hZ d ν V a *
      (V a.1)⁻¹ ^ markedMemoryIndependentRunCount hZ d a *
      markedMemoryIndependentEndpointScalar hZ d q a) /
      markedMemoryIndependentBirthFactorials hZ d : ℝ) : ℂ) *
    markedMemoryHistoryEdgeResidualProduct hZ ψ η d₀ Y Q χ n 0 H

theorem markedMemoryNormalizedEndpointWeight_eq
    (i : MarkedMemoryNormalizedHistoryIndex (A := A) (n := n) hZ s) :
    markedMemoryNormalizedEndpointWeight hZ s ν V ψ η d₀ Y Q q χ i=
      markedMemoryChronologicalWeight ν V hZ ψ η d₀ Y Q 1
        (markedMemoryHistoryVisitSchedule q n) χ n 0 (markedMemoryNormalizedHistoryAssembly hZ s i) := by
  rcases i with ⟨⟨⟨f,hs⟩,order⟩,hn⟩
  cases hs
  simpa only [markedMemoryNormalizedEndpointWeight,markedMemoryIndependentEndpointScalar_eq,
    markedMemoryNormalizedHistoryAssembly,markedMemoryFiniteHistoryAssembly,markedMemoryHistoryTransport] using
      (markedMemoryIndependent_source_lifespan_weight hZ (markedMemoryFiniteTableau_toIndependent hZ f)
        order ψ η d₀ Y Q χ ν V q).symm

end
end ArtinMatthews
