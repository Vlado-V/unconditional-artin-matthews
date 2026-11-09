module

public import ArtinMatthews.MarkedMemoryIndependentLifespans
public import Mathlib.Data.List.FinRange


set_option backward.privateInPublic true
@[expose] public section

/-! Ordered distinct batches have a genuine finite encoding.  The
length is bounded by the cardinality of the identity type, while its
order remains part of the data. -/
namespace ArtinMatthews
noncomputable section

def MarkedMemoryFiniteList (A : Type*) [Fintype A] :=
  {d : (Σ k : Fin (Fintype.card A+1),Fin k.1 → A) // Function.Injective d.2}

instance {A : Type*} [Fintype A] : Fintype (MarkedMemoryFiniteList A) := by
  classical
  unfold MarkedMemoryFiniteList
  infer_instance

def markedMemoryFiniteList_toList {A : Type*} [Fintype A]
    (d : MarkedMemoryFiniteList A) : List A := List.ofFn d.1.2

theorem markedMemoryFiniteList_nodup {A : Type*} [Fintype A]
    (d : MarkedMemoryFiniteList A) : (markedMemoryFiniteList_toList d).Nodup :=
  List.nodup_ofFn_ofInjective d.2

def markedMemoryFiniteList_ofList {A : Type*} [Fintype A]
    (l : List A) (h : l.Nodup) : MarkedMemoryFiniteList A :=
  ⟨⟨⟨l.length,Nat.lt_succ_of_le h.length_le_card⟩,l.get⟩,h.injective_get⟩

@[simp] theorem markedMemoryFiniteList_toList_ofList {A : Type*} [Fintype A]
    (l : List A) (h : l.Nodup) :
    markedMemoryFiniteList_toList (markedMemoryFiniteList_ofList l h)=l := List.ofFn_get l

theorem markedMemoryFiniteList_toList_injective {A : Type*} [Fintype A] :
    Function.Injective (markedMemoryFiniteList_toList (A := A)) := by
  rintro ⟨⟨k,f⟩,hf⟩ ⟨⟨l,g⟩,hg⟩ h
  have he : k.1=l.1 := by
    simpa only [markedMemoryFiniteList_toList,List.length_ofFn] using congrArg List.length h
  have hkl : k=l := Fin.ext he
  cases hkl
  have hfg : f=g := List.ofFn_injective h
  cases hfg
  rfl

end
end ArtinMatthews
