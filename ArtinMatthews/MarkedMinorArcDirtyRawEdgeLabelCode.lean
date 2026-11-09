module

public import ArtinMatthews.MarkedMinorArcDirtyRawEdgeIndices


set_option backward.privateInPublic true
@[expose] public section

/-! Actual promotion/fresh labels inject into independent finite group
patterns, indexed promotions, and fresh-only product coordinates. -/
noncomputable section
namespace ArtinMatthews

theorem markedDirtyEdgeFreshGroups_eq_compl {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} {B : ℕ} {m : MarkedRawMemory P B}
    (prom : MarkedRawEdgePromotions m) :
    markedDirtyEdgeFreshGroups prom=Finset.univ \ markedDirtyEdgePromotedGroups prom := by
  classical
  ext j
  simp only [markedDirtyEdgeFreshGroups,markedDirtyEdgePromotedGroups,Finset.mem_filter,
    Finset.mem_univ,true_and,Finset.mem_sdiff,not_not]

def markedDirtyEdgeComplementFreshTuple {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} {B : ℕ} (m : MarkedRawMemory P B)
    (prom : MarkedRawEdgePromotions m) (fresh : MarkedRawEdgeFreshLabels prom) :
    (j : ↥(Finset.univ \ markedDirtyEdgePromotedGroups prom)) → ↥(P j.1) :=
  fun j => markedRawEdgeTargetLast m prom fresh j.1

theorem markedDirtyEdgeComplementFreshTuple_injective {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} {B : ℕ} (m : MarkedRawMemory P B)
    (prom : MarkedRawEdgePromotions m) :
    Function.Injective (markedDirtyEdgeComplementFreshTuple m prom) := by
  intro a b hab
  apply markedDirtyEdgeFreshTuple_injective m prom
  funext j
  exact congrFun hab ⟨j.1,by rw [← markedDirtyEdgeFreshGroups_eq_compl]; exact j.2⟩

abbrev MarkedDirtyEdgeLabelCode {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} {B : ℕ} (m : MarkedRawMemory P B) :=
  Σ code : (Σ I : Finset J, MarkedRawPromotionTuple m I), (j : ↥(Finset.univ \ code.1)) → ↥(P j.1)

def markedDirtyEdgeLabelCode {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} {B : ℕ} (m : MarkedRawMemory P B)
    (labels : Σ prom : MarkedRawEdgePromotions m, MarkedRawEdgeFreshLabels prom) : MarkedDirtyEdgeLabelCode m :=
  ⟨markedDirtyEdgePromotionCode labels.1,markedDirtyEdgeComplementFreshTuple m labels.1 labels.2⟩

theorem markedDirtyEdgeLabelCode_injective {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} {B : ℕ} (m : MarkedRawMemory P B) :
    Function.Injective (markedDirtyEdgeLabelCode m) := by
  rintro ⟨pa,fa⟩ ⟨pb,fb⟩ he
  have hc := congrArg Sigma.fst he
  change markedDirtyEdgePromotionCode pa=markedDirtyEdgePromotionCode pb at hc
  have hp := markedDirtyEdgePromotionCode_injective hc
  cases hp
  have hf : markedDirtyEdgeComplementFreshTuple m pa fa=markedDirtyEdgeComplementFreshTuple m pa fb :=
    eq_of_heq (Sigma.mk.inj_iff.mp he).2
  have heq := markedDirtyEdgeComplementFreshTuple_injective m pa hf
  cases heq
  rfl

instance markedDirtyEdgeLabelCode_fintype {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} {B : ℕ} (m : MarkedRawMemory P B) :
    Fintype (MarkedDirtyEdgeLabelCode m) := by
  classical
  unfold MarkedDirtyEdgeLabelCode
  infer_instance

/-- Full actual edge choice coding into ordinary product-law coordinates;
all admissibility restrictions are retained by the injective image. -/
def markedDirtyRawEdgeChoiceIndependentCode {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (s : MarkedRawState P (pads+1) B Z)
    (choice : MarkedRawEdgeChoice hZ s) : Z × ((J → Bool) × MarkedDirtyEdgeLabelCode s.2.2) :=
  (choice.target,(choice.store,markedDirtyEdgeLabelCode s.2.2 ⟨choice.promotions,choice.fresh⟩))

theorem markedDirtyRawEdgeChoiceIndependentCode_injective {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (s : MarkedRawState P (pads+1) B Z) :
    Function.Injective (markedDirtyRawEdgeChoiceIndependentCode hZ s) := by
  intro a b hab
  have ht := congrArg Prod.fst hab
  have hh := congrArg Prod.snd hab
  have hs := congrArg Prod.fst hh
  have hlabels := congrArg Prod.snd hh
  apply markedRawEdgeChoiceCode_injective hZ s
  apply Prod.ext
  · exact ht
  · apply Prod.ext
    · exact hs
    · exact markedDirtyEdgeLabelCode_injective s.2.2 hlabels

end ArtinMatthews
