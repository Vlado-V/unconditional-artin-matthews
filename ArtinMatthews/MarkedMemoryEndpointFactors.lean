module

public import ArtinMatthews.MarkedMemoryEndpointDecorations
public import ArtinMatthews.MarkedMemoryNormalizedEndpointWeight
public import ArtinMatthews.MarkedMemoryHistoryEdgeProduct


set_option backward.privateInPublic true
@[expose] public section

/-! The prime/run/source-scalar numerator depends only on the bare
endpoint family. The factorial denominator is exactly its birth-order
fiber size; all ordered edge kernels remain literal. -/
namespace ArtinMatthews
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.decEq Classical.propDecidable

variable {J : Type*} [Fintype J] {A : J → Type*}
  [∀ j,Fintype (A j)] [∀ j,DecidableEq (A j)]
  {P : J → Finset Nat.Primes} {pads B n : ℕ} {Z : Finset (ℤ × ℤ)}
  (hZ : ∀ z ∈ Z,IsCoprime z.1 z.2) (s : MarkedRawState P (pads+1) B Z)
  (e : MarkedMemoryEndpointFamily (A := A) (n := n) hZ s)

def markedMemoryEndpointIndependent (births : MarkedMemoryEndpointBirthOrders e.1) :
    MarkedMemoryIndependentLifespans (A := A) (P := P) (pads := pads) (B := B) hZ n :=
  markedMemoryFiniteTableau_toIndependent hZ (markedMemoryEndpointFamilyTableau hZ s e births)

def markedMemoryEndpointRunCount (a : Σ j,A j) : ℕ :=
  (Finset.univ.filter (fun v : Fin n =>
    (markedMemoryEndpointBase e.1).incomingAt (2*v.val+1) a.1=a.2 ∧
    (e.1.first a.1 a.2).val≤2*v.val+1 ∧ 2*v.val+1≤(e.1.last a.1 a.2).val ∧
    ¬ (markedMemoryEndpointBase e.1).activeAt (2*v.val+1) a.1 a.2)).card

theorem markedMemoryEndpoint_runCount (births : MarkedMemoryEndpointBirthOrders e.1) (a : Σ j,A j) :
    markedMemoryIndependentRunCount hZ (markedMemoryEndpointIndependent hZ s e births) a =
      markedMemoryEndpointRunCount hZ s e a := by
  unfold markedMemoryIndependentRunCount markedMemoryEndpointRunCount
  apply congrArg Finset.card
  ext v
  have hm := markedMemoryPendingQueueAt_mem
    ((markedMemoryEndpointIndependent hZ s e births).lifespan a.1) (2*v.val+1) (by omega) a.2
  constructor
  · intro hv
    have h := (Finset.mem_filter.mp hv).2
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,h.1,hm.mp h.2⟩
  · intro hv
    have h := (Finset.mem_filter.mp hv).2
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,h.1,hm.mpr h.2⟩

def markedMemoryEndpointBirthMass (ν : (j : J) → ↥(P j) → ℝ) (V : J → ℝ) (a : Σ j,A j) : ℝ :=
  if (e.1.first a.1 a.2).val=0 then 1 else
    (if (e.1.first a.1 a.2).val%2=1 then V a.1 else 1)*ν a.1 (e.1.particle a.1 a.2).1

theorem markedMemoryEndpoint_birthMass (births : MarkedMemoryEndpointBirthOrders e.1)
    (ν : (j : J) → ↥(P j) → ℝ) (V : J → ℝ) (a : Σ j,A j) :
    markedMemoryIndependentBirthMass hZ (markedMemoryEndpointIndependent hZ s e births) ν V a =
      markedMemoryEndpointBirthMass hZ s e ν V a := rfl

def markedMemoryEndpointSourceScalar (q : ℝ) (a : Σ j,A j) : ℝ :=
  markedMemoryIndependentEndpointScalar hZ
    (markedMemoryEndpointIndependent hZ s e (markedMemoryEndpointCanonicalBirths e.1)) q a

theorem markedMemoryEndpoint_sourceScalar (births : MarkedMemoryEndpointBirthOrders e.1)
    (q : ℝ) (a : Σ j,A j) :
    markedMemoryIndependentEndpointScalar hZ (markedMemoryEndpointIndependent hZ s e births) q a =
      markedMemoryEndpointSourceScalar hZ s e q a := rfl

theorem markedMemoryEndpoint_birthFactorials (births : MarkedMemoryEndpointBirthOrders e.1) :
    markedMemoryIndependentBirthFactorials hZ (markedMemoryEndpointIndependent hZ s e births) =
      (markedMemoryEndpointBirthFactorial e.1 : ℝ) := by
  unfold markedMemoryIndependentBirthFactorials
  change (∏ v : Fin (n+1), ∏ j : J,
    (((markedMemoryEndpointDataDecorated e.1 births).birthsAt (2*v.val) j).length.factorial : ℝ)) = _
  simp only [MarkedMemoryFiniteTableauData.birthsAt_valid]
  simp only [markedMemoryEndpointBirthFactorial,Nat.cast_prod]
  apply Finset.prod_congr rfl
  intro v _
  apply Finset.prod_congr rfl
  intro j _
  have hk := (markedMemoryFiniteListSet_card (births v j).1).symm.trans
    (congrArg Finset.card (births v j).2)
  change ((markedMemoryFiniteList_toList (births v j).1).length.factorial : ℝ) = _
  simp only [markedMemoryFiniteList_toList,List.length_ofFn]
  exact congrArg (fun k : ℕ => (k.factorial : ℝ)) hk

def markedMemoryEndpointPrimeScalar (ν : (j : J) → ↥(P j) → ℝ) (V : J → ℝ) (q : ℝ) : ℝ :=
  ∏ a : Σ j,A j,markedMemoryEndpointBirthMass hZ s e ν V a *
    (V a.1)⁻¹^markedMemoryEndpointRunCount hZ s e a * markedMemoryEndpointSourceScalar hZ s e q a

theorem markedMemoryEndpointWeight_factor
    (births : MarkedMemoryEndpointBirthOrders e.1) (order : Fin n → J → Equiv.Perm (Fin pads))
    (ν : (j : J) → ↥(P j) → ℝ) (V : J → ℝ) (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ)
    (d₀ Y Q q : ℝ) (χ : ℕ → MarkedRawState P (pads+1) B Z → ℂ) :
    markedMemoryNormalizedEndpointWeight hZ s ν V ψ η d₀ Y Q q χ
        (markedMemoryEndpointFamilyIndex hZ s e births order) =
      ((markedMemoryEndpointPrimeScalar hZ s e ν V q /
        (markedMemoryEndpointBirthFactorial e.1 : ℝ) : ℝ) : ℂ) *
      ((Fintype.card (MarkedMemorySlotPermutations J (pads+1)) : ℂ)⁻¹)^(2*n) *
      markedMemoryHistoryRawEdgeProduct hZ ψ η d₀ Y Q χ n 0
        (markedMemoryIndependentHistory hZ (markedMemoryEndpointIndependent hZ s e births) order) := by
  unfold markedMemoryNormalizedEndpointWeight
  change (((∏ a : Σ j,A j,
      markedMemoryIndependentBirthMass hZ (markedMemoryEndpointIndependent hZ s e births) ν V a *
      (V a.1)⁻¹ ^ markedMemoryIndependentRunCount hZ (markedMemoryEndpointIndependent hZ s e births) a *
      markedMemoryIndependentEndpointScalar hZ (markedMemoryEndpointIndependent hZ s e births) q a) /
      markedMemoryIndependentBirthFactorials hZ (markedMemoryEndpointIndependent hZ s e births) : ℝ) : ℂ) *
    markedMemoryHistoryEdgeResidualProduct hZ ψ η d₀ Y Q χ n 0
      (markedMemoryIndependentHistory hZ (markedMemoryEndpointIndependent hZ s e births) order) = _
  simp only [markedMemoryEndpoint_birthMass,markedMemoryEndpoint_runCount,
    markedMemoryEndpoint_sourceScalar,markedMemoryEndpoint_birthFactorials]
  rw [markedMemoryHistoryEdgeResidualProduct_raw]
  unfold markedMemoryEndpointPrimeScalar
  ring

end
end ArtinMatthews
