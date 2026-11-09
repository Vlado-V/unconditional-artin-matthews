module

public import ArtinMatthews.MarkedMemoryFiniteListFiber
public import ArtinMatthews.MarkedMemoryFiniteAnchorNormalization


set_option backward.privateInPublic true
@[expose] public section

/-! Finite endpoint data with no stored birth order or copied-slot order.
Ghost-birth identity sets are computed from first/last/active incidence.
Initial pending memory is empty. Active-slot identity embeddings remain
explicit coordinates, distinct from the copied-slot decoration. -/
namespace ArtinMatthews
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

variable {J : Type*} [Fintype J] {A : J → Type*} [∀ j,Fintype (A j)]
  {P : J → Finset Nat.Primes} {pads n : ℕ} {Z : Finset (ℤ × ℤ)}

@[ext] structure MarkedMemoryEndpointData (A : J → Type*) [∀ j,Fintype (A j)]
    (P : J → Finset Nat.Primes) (pads : ℕ) (Z : Finset (ℤ × ℤ)) (n : ℕ) where
  first : (j : J) → A j → Fin (2*n+2)
  last : (j : J) → A j → Fin (2*n+2)
  active : Fin (2*n+2) → (j : J) → Finset (A j)
  incoming : Fin n → (j : J) → A j
  outgoing : Fin n → (j : J) → A j
  position : Fin (n+1) → Z
  activeId : Fin (n+1) → (j : J) → Fin (pads+1) ↪ A j
  particle : (j : J) → A j → MarkedRawParticle (P j)

instance markedMemoryEndpointData_finite : Finite (MarkedMemoryEndpointData A P pads Z n) := by
  classical
  let encode := fun d : MarkedMemoryEndpointData A P pads Z n =>
    (d.first,d.last,d.active,d.incoming,d.outgoing,d.position,d.activeId,d.particle)
  have he : Function.Injective encode := by
    intro a b h
    have hh : a.first=b.first ∧ a.last=b.last ∧ a.active=b.active ∧ a.incoming=b.incoming ∧
        a.outgoing=b.outgoing ∧ a.position=b.position ∧ a.activeId=b.activeId ∧ a.particle=b.particle := by
      simpa only [encode,Prod.mk.injEq] using h
    rcases hh with ⟨h₁,h₂,h₃,h₄,h₅,h₆,h₇,h₈⟩
    exact MarkedMemoryEndpointData.ext h₁ h₂ h₃ h₄ h₅ h₆ h₇ h₈
  exact Finite.of_injective encode he

instance markedMemoryEndpointData_fintype : Fintype (MarkedMemoryEndpointData A P pads Z n) := Fintype.ofFinite _

def markedMemoryEndpointOfData (d : MarkedMemoryFiniteTableauData A P pads Z n) :
    MarkedMemoryEndpointData A P pads Z n :=
  ⟨d.first,d.last,d.active,d.incoming,d.outgoing,d.position,d.activeId,d.particle⟩

def markedMemoryEndpointDecorateData (d : MarkedMemoryEndpointData A P pads Z n)
    (births : Fin (n+1) → (j : J) → MarkedMemoryFiniteList (A j)) :
    MarkedMemoryFiniteTableauData A P pads Z n where
  first := d.first
  last := d.last
  active := d.active
  initial := fun _ => markedMemoryFiniteList_ofList [] (List.nodup_nil)
  births := births
  incoming := d.incoming
  outgoing := d.outgoing
  position := d.position
  activeId := d.activeId
  particle := d.particle

def markedMemoryEndpointBase (d : MarkedMemoryEndpointData A P pads Z n) :
    MarkedMemoryFiniteTableauData A P pads Z n :=
  markedMemoryEndpointDecorateData d (fun _ _ => markedMemoryFiniteList_ofList [] List.nodup_nil)


def markedMemoryEndpointBirthSet (d : MarkedMemoryEndpointData A P pads Z n)
    (v : Fin (n+1)) (j : J) : Finset (A j) :=
  Finset.univ.filter (fun a => (d.first j a).val=2*v.val+1 ∧ 2*v.val+1≤(d.last j a).val ∧
    ¬ (markedMemoryEndpointBase d).activeAt (2*v.val) j a)

abbrev MarkedMemoryEndpointBirthOrders (d : MarkedMemoryEndpointData A P pads Z n) :=
  (v : Fin (n+1)) → (j : J) →
    {l : MarkedMemoryFiniteList (A j) // markedMemoryFiniteListSet l=markedMemoryEndpointBirthSet d v j}

def markedMemoryEndpointCanonicalBirths (d : MarkedMemoryEndpointData A P pads Z n) :
    MarkedMemoryEndpointBirthOrders d :=
  fun v j => ⟨markedMemoryFiniteListCanonical (markedMemoryEndpointBirthSet d v j),
    markedMemoryFiniteListCanonical_set _⟩

def markedMemoryEndpointDataDecorated (d : MarkedMemoryEndpointData A P pads Z n)
    (births : MarkedMemoryEndpointBirthOrders d) : MarkedMemoryFiniteTableauData A P pads Z n :=
  markedMemoryEndpointDecorateData d (fun v j => (births v j).1)

theorem markedMemoryEndpointOfData_decorated (d : MarkedMemoryEndpointData A P pads Z n)
    (births : MarkedMemoryEndpointBirthOrders d) :
    markedMemoryEndpointOfData (markedMemoryEndpointDataDecorated d births)=d := by
  cases d
  rfl

theorem markedMemoryEndpoint_births_mem (d : MarkedMemoryEndpointData A P pads Z n)
    (births : MarkedMemoryEndpointBirthOrders d) (v : Fin (n+1)) (j : J) (a : A j) :
    a ∈ (markedMemoryEndpointDataDecorated d births).birthsAt (2*v.val) j ↔
      (d.first j a).val=2*v.val+1 ∧ 2*v.val+1≤(d.last j a).val ∧
        ¬ (markedMemoryEndpointBase d).activeAt (2*v.val) j a := by
  rw [MarkedMemoryFiniteTableauData.birthsAt_valid]
  exact (markedMemoryFiniteListSet_mem _ _).symm.trans
    ((by rw [(births v j).2]; simp only [markedMemoryEndpointBirthSet,Finset.mem_filter,Finset.mem_univ,true_and]) : a ∈ markedMemoryFiniteListSet (births v j).1 ↔ _)

theorem markedMemoryEndpoint_birthsAt_mem (d : MarkedMemoryEndpointData A P pads Z n)
    (births : MarkedMemoryEndpointBirthOrders d) (t : ℕ) (ht : t < 2*n+1) (he : t%2=0)
    (j : J) (a : A j) :
    a ∈ (markedMemoryEndpointDataDecorated d births).birthsAt t j ↔
      (d.first j a).val=t+1 ∧ t+1≤(d.last j a).val ∧ ¬ (markedMemoryEndpointBase d).activeAt t j a := by
  have hv : t/2 < n+1 := by omega
  have htime : 2*(t/2)=t := by omega
  simpa only [htime] using markedMemoryEndpoint_births_mem d births ⟨t/2,hv⟩ j a

theorem markedMemoryEndpointBirthOrders_card (d : MarkedMemoryEndpointData A P pads Z n) :
    Fintype.card (MarkedMemoryEndpointBirthOrders d) =
      ∏ v : Fin (n+1), ∏ j : J, (markedMemoryEndpointBirthSet d v j).card.factorial := by
  rw [Fintype.card_pi]
  apply Finset.prod_congr rfl
  intro v _
  rw [Fintype.card_pi]
  exact Finset.prod_congr rfl (fun j _ => markedMemoryFiniteListFiber_card _)

def markedMemoryEndpointBirthFactorial (d : MarkedMemoryEndpointData A P pads Z n) : ℕ :=
  ∏ v : Fin (n+1), ∏ j : J, (markedMemoryEndpointBirthSet d v j).card.factorial

theorem markedMemoryEndpointBirthFactorial_pos (d : MarkedMemoryEndpointData A P pads Z n) :
    0 < markedMemoryEndpointBirthFactorial d := by
  unfold markedMemoryEndpointBirthFactorial
  exact Finset.prod_pos (fun _ _ => Finset.prod_pos (fun _ _ => Nat.factorial_pos _))

end
end ArtinMatthews
