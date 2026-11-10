module

public import ArtinMatthews.GiantSignedUniformBirthRank
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

/-! Order the actual uniform addresses by operation, finite band rank,
and the literal initial slot, canonical edge slot or ghost batch index. -/
namespace ArtinMatthews
noncomputable section

def giantSignedBirthOperationTime {n : ℕ} : GiantSignedBirthOperation n → ℕ
  | .initial => 0
  | .visit i => 2*i.val+1
  | .edge i => 2*i.val+2

theorem giantSignedBirthOperationTime_injective {n : ℕ} :
    Function.Injective (giantSignedBirthOperationTime (n := n)) := by
  intro a b h
  cases a <;> cases b <;> simp only [giantSignedBirthOperationTime] at h <;> try omega
  all_goals first | rfl | (congr 1; apply Fin.ext; omega)

theorem giantSignedBirthOperationTime_lt {n : ℕ} (o : GiantSignedBirthOperation n) :
    giantSignedBirthOperationTime o < 2*n+2 := by
  cases o <;> simp only [giantSignedBirthOperationTime] <;> omega

variable {B : Type*} {M n H : ℕ}

def giantSignedUniformBirthGroup : GiantSignedUniformBirthAddress B M n H → B
  | .inl a => a.1
  | .inr (.inl a) => a.2.1
  | .inr (.inr a) => a.2.1

def giantSignedUniformBirthSlot : GiantSignedUniformBirthAddress B M n H → ℕ
  | .inl a => a.2.val
  | .inr (.inl a) => a.2.2.val
  | .inr (.inr a) => a.2.2.val

def giantSignedUniformBirthTime (a : GiantSignedUniformBirthAddress B M n H) : ℕ :=
  giantSignedBirthOperationTime (giantSignedUniformBirthOperation M n H a)

variable [Fintype B]

def giantSignedUniformBirthChronologicalKey (a : GiantSignedUniformBirthAddress B M n H) :
    ℕ ×ₗ (Fin (Fintype.card B) ×ₗ ℕ) :=
  toLex (giantSignedUniformBirthTime a,
    toLex (Fintype.equivFin B (giantSignedUniformBirthGroup a), giantSignedUniformBirthSlot a))

theorem giantSignedUniformBirthChronologicalKey_injective :
    Function.Injective (giantSignedUniformBirthChronologicalKey (B := B) (M := M) (n := n) (H := H)) := by
  intro a b h
  have ht := congrArg (fun u : ℕ ×ₗ (Fin (Fintype.card B) ×ₗ ℕ) => (ofLex u).1) h
  have hg := congrArg (fun u : ℕ ×ₗ (Fin (Fintype.card B) ×ₗ ℕ) => (ofLex (ofLex u).2).1) h
  have hs := congrArg (fun u : ℕ ×ₗ (Fin (Fintype.card B) ×ₗ ℕ) => (ofLex (ofLex u).2).2) h
  change giantSignedUniformBirthTime a = giantSignedUniformBirthTime b at ht
  change Fintype.equivFin B (giantSignedUniformBirthGroup a) =
    Fintype.equivFin B (giantSignedUniformBirthGroup b) at hg
  change giantSignedUniformBirthSlot a = giantSignedUniformBirthSlot b at hs
  have ho := giantSignedBirthOperationTime_injective ht
  have hj := (Fintype.equivFin B).injective hg
  rcases a with ⟨ga,sa⟩ | ⟨ia,ga,sa⟩ | ⟨ia,ga,sa⟩ <;>
    rcases b with ⟨gb,sb⟩ | ⟨ib,gb,sb⟩ | ⟨ib,gb,sb⟩ <;>
    simp only [giantSignedUniformBirthOperation, giantSignedUniformBirthGroup,
      giantSignedUniformBirthSlot] at ho hj hs <;> cases ho
  all_goals
    cases hj
    have hslot : sa = sb := Fin.ext hs
    cases hslot
    rfl

@[instance_reducible]
def giantSignedUniformBirthChronologicalOrder :
    LinearOrder (GiantSignedUniformBirthAddress B M n H) :=
  LinearOrder.lift' giantSignedUniformBirthChronologicalKey
    giantSignedUniformBirthChronologicalKey_injective

def GiantSignedUniformBirthEarlier (a b : GiantSignedUniformBirthAddress B M n H) : Prop :=
  giantSignedUniformBirthChronologicalKey a < giantSignedUniformBirthChronologicalKey b

theorem giantSignedUniformBirthEarlier_iff (a b : GiantSignedUniformBirthAddress B M n H) :
    GiantSignedUniformBirthEarlier a b ↔
      giantSignedUniformBirthTime a < giantSignedUniformBirthTime b ∨
      giantSignedUniformBirthOperation M n H a = giantSignedUniformBirthOperation M n H b ∧
        (Fintype.equivFin B (giantSignedUniformBirthGroup a) <
            Fintype.equivFin B (giantSignedUniformBirthGroup b) ∨
          giantSignedUniformBirthGroup a = giantSignedUniformBirthGroup b ∧
            giantSignedUniformBirthSlot a < giantSignedUniformBirthSlot b) := by
  unfold GiantSignedUniformBirthEarlier giantSignedUniformBirthChronologicalKey giantSignedUniformBirthTime
  rw [Prod.Lex.toLex_lt_toLex, Prod.Lex.toLex_lt_toLex,
    giantSignedBirthOperationTime_injective.eq_iff, (Fintype.equivFin B).injective.eq_iff]

theorem giantSignedUniformBirthEarlier_time {a b : GiantSignedUniformBirthAddress B M n H}
    (h : GiantSignedUniformBirthEarlier a b) : giantSignedUniformBirthTime a ≤ giantSignedUniformBirthTime b :=
  Prod.Lex.monotone_fst _ _ (le_of_lt h)

end
end ArtinMatthews
